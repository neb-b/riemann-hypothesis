module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem genBC_frameR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S]
    [CommRing K] (x : Sp S ⟶ Xo.X) (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChangeR hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

theorem bcGenR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (c : Coeff l) :
    BcGenRSt Xo c := fun _ _ _ _ ψ y =>
  ⟨secCP (cpS ψ.toRingHom y.x) y.s, fun _ _ => rfl, genBC_frameR hS hT y.x ψ.toRingHom y.s y.gen⟩

theorem bcLieAll (c : Coeff l) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left)
    (hw : IsTanAt (spMap ψ.toRingHom ≫ y.x) w) (he : IsEigAt c τ w) : ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  let x := spMap ψ.toRingHom ≫ y.x
  have tn : ∀ τ i, IsTanAt x (spMap (dualMap ψ.toRingHom) ≫ y.u τ i) := fun τ i => tan_bc ψ.toRingHom (y.tan τ i)
  refine eig_basis_of_full (fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) tn (fun τ i => eig_bc ψ τ (y.eig τ i))
    (fun m => ?_) τ w hw he
  have h := hS (Xo := Xo) x
  choose u' hu' using fun i => push_surj h (tv (tvOf (tn (eB Dw i).1 (eB Dw i).2)))
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback y.x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  have gp := Chart.isGrpPullback_factor y.x (spMap ψ.toRingHom) h
  have bs : IsLieBasis u' := Chart.frameLieBCR _ (uS_basis y) ψ.toRingHom gp (fun a b v hv => push_inj h (by
      have := smT_add x _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc]
      exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (push_uS y i)).symm)
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (uS y i)).symm)
      exact (spMap_comp_spMap _ _).trans ((congrArg spMap (dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)
  obtain ⟨p, hp⟩ := push_surj h (tv m)
  have key : ∀ a, IsLieComb a u' p ↔ m = ∑ k, a ((eB Dw).symm k) • tvOf (tn k.1 k.2) := fun a => by
    rw [isLieComb_iff h, hp, ← (eB Dw).sum_comp]
    simp only [Equiv.symm_apply_apply, hu']
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum]; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum]; rfl)⟩
  obtain ⟨a, ha, hu⟩ := bs.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem m))
  refine ⟨fun k => a ((eB Dw).symm k), (key a).1 ha, fun b hb => ?_⟩
  have := hu (fun i => b (eB Dw i)) ((key _).2 (by simpa using hb))
  funext k; rw [← this]; simp

theorem bcLieR (c : Coeff l) : BcLieRSt Xo c := fun _ _ _ _ ψ y => bcLieAll c ψ y

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeI
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ = dualMap φ := RingHom.ext fun _ => rfl

section BC

variable {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S)

theorem hw0 (i : Fin (Fintype.card (IxB Dw))) :
    (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ.toRingHom) ≫ (uS y i).left) ≫
      ((Over.pullback y.x).obj Xo.univ.t.G).hom = (epsR T).hom ≫ spMap ψ.toRingHom := by
  rw [Category.assoc, Over.w (uS y i)]
  show spMap _ ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap _
  rw [spMap_comp_spMap, spMap_comp_spMap, dualMapR_eq, dualMap_comp_alg]

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSt
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR

theorem snd_pow_left {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) (N : ℕ) :
    (snd T A ^ N).left = (snd T A).left ≫ (mulA A N).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id]

theorem sval_zc {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem vtOver_move {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) (N : ℕ) {ok : (T₀ ⟶ t.G) → Prop} (hok : ∀ u, ok u → u ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow t.G t.PP.L 1 T₀)} {tt : T₀ ⟶ t.G} {F : LB.Sec (LPow t.G t.PP.L ((N : ℤ) ^ 2) T₀)}
    (h : IsVtOver t.G t.PP N ok s₀ tt F) {s : LB.Sec (LPow t'.G t'.PP.L 1 T)} (hs : TieT m.cart τ hτ w 1 s₀ s) :
    ∃ F' : LB.Sec (LPow t'.G t'.PP.L ((N : ℤ) ^ 2) T),
      IsVtOver t'.G t'.PP N (fun u => u ^ (N ^ 2) = 1) s (liftPt m.cart τ hτ tt) F' ∧
        TieT m.cart τ hτ w ((N : ℤ) ^ 2) F F' := by
  obtain ⟨t₀', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  have h1 : (liftPt m.cart τ hτ t₀').left ≫ m.φ = τ ≫ t₀'.left := liftPt_left m.cart τ hτ t₀'
  have ht1 : liftPt m.cart τ hτ t₀' ^ N = liftPt m.cart τ hτ tt :=
    pt_ext m.cart ((pow_rel m.cart τ hτ h1 N).trans (by rw [ht]; exact (liftPt_left m.cart τ hτ tt).symm))
  have o1 : liftPt m.cart τ hτ t₀' ^ (N ^ 2) = 1 := pow_eq_one m.cart τ hτ h1 (hok _ o)
  obtain ⟨α₀', g₀', pm₀, n₀'⟩ := mulGen_move m w hw N α₀ g₀ n₀
  have eα : ∀ k, (![(snd T₀ t.G).left, (snd T₀ t.G ^ N).left] : Fin 2 → _) k =
      (snd T₀ t.G).left ≫ (![𝟙 t.G.left, (mulA t.G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.comp_id _).symm
    · exact snd_pow_left _ _ _
  obtain ⟨α₁, gα₁, Hα₁⟩ := exists_gen_pull (L := t.PP.L) ![𝟙 t.G.left, (mulA t.G N).left] ![(N : ℤ) ^ 2, -1] α₀
    (snd T₀ t.G).left _ eα
  have gα := gα₁ g₀
  have vα : ∀ y J, Good t.PP.L y J → val α (𝟙 _) y J = val α₁ (𝟙 _) y J := fun y J hJ =>
    (val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_of_pull eα Hα₁ _ y hJ).symm)
  have tw' : IsTwistPull t.G t.PP.L (mulT t.G T₀ N) (snd T₀ t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α₁ s₀ s₁ :=
    twist_of_val t.PP.isLB gα fun y J hJ => (twist_val tw (𝟙 _) y hJ).trans (by rw [vα y J hJ, Category.id_comp])
  obtain ⟨α', gα', pmα, cα'⟩ := MixEnd.genSnd_move m.cart τ hτ t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw.1)
    (mulA t'.G N).left (mulA t.G N).left (mulA_push m.cart N) ![(N : ℤ) ^ 2, -1] α₀' α₀ pm₀ (snd T t'.G ^ N)
    (snd T₀ t.G ^ N) (snd_pow_left _ _ _) (snd_pow_left _ _ _) _ gα
    (corr_of_val t.PP.isLB fun y J hJ => (val_of_pull eα Hα₁ _ y hJ).trans (val_pull hJ _ _ _).symm)
  obtain ⟨s₁', tw1, hs1⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := mulT t'.G T N) (mA := snd T t'.G ^ N)
    (lift_snd _ _) (mulT_push m.cart τ hτ N) (snd_pow_push m.cart τ hτ N) gα' pmα tw' hs
  obtain ⟨U', sl', pmU⟩ := symLift_move m.cart τ hτ t.PP.isLB t'.PP.isLB w hw.1 sl (hok _ o) h1
  have hxU : τ ≫ U.pt.left = U'.pt.left ≫ m.φ := by rw [sl.pt_eq, sl'.pt_eq]; exact h1.symm
  obtain ⟨F', ac', hF⟩ := twist_move m.cart τ hτ t'.PP.isLB w (ψA := translT t'.G U'.pt)
    (mA := translPt t'.G U'.pt) (lift_snd _ _) (psi_transl m.cart τ hτ U'.pt U.pt hxU)
    (psi_tr m.cart τ hτ U'.pt U.pt hxU).symm U'.isGen pmU ac hs1
  exact ⟨F', ⟨liftPt m.cart τ hτ t₀', α₀', α', s₁', U', ht1, o1, g₀', n₀', cα', tw1, sl', ac'⟩, hF⟩

theorem vtMoveSt : VtMoveSt := by
  intro E _ _ _ H X₀ t₀ K _ x tK m1 w1 hw N ok s tt F hF hok sK hsK
  have hfst : ∀ {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
      r ≫ (fst (𝟙_ (Over (Sp K))) tK.G).left ≫ (𝟙_ (Over (Sp K))).hom = (r ≫ (snd _ tK.G).left) ≫ tK.G.hom := by
    intro Z r
    rw [Over.w (fst _ _), Category.assoc, Over.w (snd _ _)]
  have hs : TieT m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl w1 1 s (zCast tK.G Nat.cast_one sK) := by
    intro Z r z J₀ J hJ₀ hJ
    have e := hsK Z (r ≫ (snd _ tK.G).left) (r ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left) r
      (by rw [Category.assoc, psi_snd, Category.assoc])
      (by rw [Category.assoc, psi_fst]; exact hfst r) rfl z J₀ J hJ₀ hJ
    rw [sval_zc, Category.comp_id] at e
    rw [sval_zc, e, zpow_one, pow_one]
    rfl
  obtain ⟨F', hV, hT⟩ := vtOver_move m1 w1 hw (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl N hok hF hs
  refine ⟨_, F', hV, fun Z r zp zp' h1 h2 h3 z J J' hJ hJ' => ?_⟩
  subst h3
  obtain rfl : zp = zp' ≫ (psiO m1.cart (T₀ := Over.mk x) (𝟙_ (Over (Sp K))).hom rfl).left := by
    refine hom_ext₀ ?_ ?_
    · rw [Category.assoc, psi_fst, h2, hfst]
    · rw [Category.assoc, psi_snd, h1, Category.assoc]
  rw [sval_zc, sval_zc, hT Z zp' z J J' hJ hJ', Category.comp_id]
  congr 1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end

