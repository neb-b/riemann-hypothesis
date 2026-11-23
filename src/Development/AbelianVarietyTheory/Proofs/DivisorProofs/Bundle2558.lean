module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.ThetaParity

theorem exists_rigPull_inv {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    haveI := P.isAb.comm
    ∃ w : LB.Iso P.L (P.L.pull (ι[P.A]).left), GlobalTheory.OneBasis.RigPull P.A P.A (𝟙 S) (ι[P.A]).left w rig rig := by
  haveI := P.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.exists_gen_neg_of_sym GlobalTheory.globalFns_holds P.isAb P.isLB P.sym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.AbPackage.exists_rigidified_sym P.isLB u hu
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨he, w, hw, hm⟩ := GlobalTheory.SymmetricBundle.isSymmetric_of_gen L s hs hr
  refine ⟨w, GlobalTheory.SabBaseChange.isGrpPullback_inv P.A, hw, hrig, ?_⟩
  exact (maps_iff w (K := PUnit) (fun _ => eSec P.A) (fun _ => eSec P.A) (fun _ => 1) rig rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he P.L j) (fun _ => rfl)).1 hm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem pt_neg {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) : ρ.pt (-a) = (ρ.pt a)⁻¹ := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    have h' : ρ.pt 0 * ρ.pt 0 = ρ.pt 0 * 1 := by rw [_root_.mul_one]; exact h.symm
    exact mul_left_cancel h'
  have h := ρ.pt_add (-a) a
  rw [neg_add_cancel, h0] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pt_neg_left {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) :
    haveI := ρ.P.isAb.comm
    (ρ.pt (-a)).left ≫ (ι[ρ.P.A]).left = 𝟙 _ ≫ (ρ.pt a).left := by
  rw [pt_neg, Category.id_comp, ← Over.comp_left]
  congr 1
  simp [Hom.inv_def]

theorem key_fn (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ c₀ : Γ((baseOver (Sp S.R)).left, ⊤), ∀ a, ∃ d : Γ((baseOver (Sp S.R)).left, ⊤),
      d ^ ((S.r * S.N) ^ 2) = 1 ∧ c₀ * fn (⟨S.th (-a), S.th_mem (-a)⟩ : S.R) = d * fn (⟨S.th a, S.th_mem a⟩ : S.R) := by
  haveI := ρ.P.isAb.comm
  obtain ⟨w, R⟩ := exists_rigPull_inv ρ.P ρ.rig ρ.rig_gen
  have hφ : (ι[ρ.P.A]).left ≫ ρ.P.A.hom = ρ.P.A.hom ≫ 𝟙 _ := by rw [Over.w, Category.comp_id]
  obtain ⟨s', hs', -⟩ := GlobalTheory.OneBasis.Calc.existsUnique_thru (k := 1) (T := baseOver (Sp S.R))
    (T' := baseOver (Sp S.R)) hφ R.2.1 ρ.P.isLB ρ.P.isLB (h := 𝟙 _) (by simp) ρ.th₁
  obtain ⟨c, hc, -⟩ := ρ.th₁_basis s'
  refine ⟨c 0, fun a => ?_⟩
  obtain ⟨e', he', He⟩ := GlobalTheory.OneBasis.TabMap.frame_move R (h := 𝟙 _) (pt_neg_left ρ a) (ρ.fr_tors a)
  have v₁ := He 1 ρ.th₁ s' (fn (⟨S.th a, S.th_mem a⟩ : S.R)) hs' (fun z J hJ => by
    have := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val a) (𝟙 _) hJ
    rw [Category.id_comp] at this
    rw [GlobalTheory.FrameMove.val_powFrame]
    simpa using this)
  have v₂ := (GlobalTheory.OneBasis.Calc.cmb_iff ρ.P.isLB (k := 1) (fun _ => ρ.th₁) c s').1 hc
  obtain ⟨d, hd⟩ := GlobalTheory.AbPackage.exists_unit_ratio ρ.P.isLB he'.2.1 (ρ.fr_tors (-a)).2.1
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull GlobalTheory.globalFns_holds ρ.P (S.r * S.N) (baseOver (Sp S.R))

  refine ⟨(d : Γ((baseOver (Sp S.R)).left, ⊤)), ?_, ?_⟩
  · have hu : d ^ ((S.r * S.N) ^ 2) = 1 := by
      apply Units.ext
      apply fn_ext
      intro z _
      obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
      have t₁ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα he' hJ
      have t₂ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα (ρ.fr_tors (-a)) hJ
      have e := hd _ (𝟙 _) z J hJ
      rw [e, mul_pow, ← t₂, _root_.mul_assoc] at t₁
      have g := mul_eq_right.1 t₁
      rw [gs_unit (𝟙 _) z ⊤ trivial, gs_unit (𝟙 _) z ⊤ trivial, map_pow, g, map_one]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · apply fn_ext
    intro z _
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
    have a₁ := v₁ z J hJ
    have a₂ := v₂ _ (ptSecT ρ.P.A (ρ.pt (-a))).left z J hJ
    have a₃ := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val (-a)) (𝟙 _) hJ
    have a₄ := hd _ (𝟙 _) z J hJ
    rw [Category.id_comp] at a₃
    rw [gs_mul _ z ⊤ trivial, gs_mul _ z ⊤ trivial]

    simp only [GlobalTheory.FrameGen.sv, Fin.sum_univ_one] at a₂
    have f₁ : (ptSecT ρ.P.A (ρ.pt (-a))).left ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]
    rw [f₁, ← GlobalTheory.FrameGen.gs_top, a₃] at a₂
    have hp : ∀ u : ((baseOver (Sp S.R)).left.presheaf.stalk z)ˣ, u ^ ((1 : ℕ) : ℤ) = u := fun u => by simp
    rw [GlobalTheory.FrameMove.val_powFrame, hp, a₄, Units.val_mul] at a₁
    have e := a₂.symm.trans a₁
    rw [← gs_unit (𝟙 _) z ⊤ trivial d] at e
    refine (Units.mul_left_inj (Geo.Tor.val (ρ.fr (-a)) (𝟙 _) z J)).1 ?_
    linear_combination e

theorem key (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ C : Ω, ∀ a, ∃ D : Ω, D ^ ((S.r * S.N) ^ 2) = 1 ∧ C * S.th (-a) = D * S.th a := by
  obtain ⟨c₀, h⟩ := key_fn S ρ
  let φ : Γ((baseOver (Sp S.R)).left, ⊤) →+* Ω :=
    S.R.val.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom.hom
  have hφ : ∀ x : S.R, φ (fn x) = x := fun x => by simp [φ, fn]
  refine ⟨φ c₀, fun a => ?_⟩
  obtain ⟨d, hd, e⟩ := h a
  refine ⟨φ d, by rw [← map_pow, hd, map_one], ?_⟩
  have := congrArg φ e
  rwa [map_mul, map_mul, hφ, hφ] at this

theorem odd_rN (S : ThetaSys o Ω) (ρ : S.Real) : Odd ((S.r * S.N) ^ 2) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ((ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)).pow

end GlobalTheory.ThetaParity

namespace GlobalTheory.ThetaParity

theorem theta_neg : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  intro o Ω _ _ _ _ S ρ a
  obtain ⟨C, hC⟩ := key S ρ
  have hodd := odd_rN S ρ
  set m := (S.r * S.N) ^ 2 with hm
  obtain ⟨x, hx⟩ := S.th_ne
  obtain ⟨D₁, hD₁, e₁⟩ := hC x
  obtain ⟨D₂, hD₂, e₂⟩ := hC (-x)
  rw [neg_neg] at e₂
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have nz : ∀ D : Ω, D ^ m = 1 → D ≠ 0 := fun D h h0 => by
    rw [h0, zero_pow hm0] at h; exact zero_ne_one h
  have hx' : S.th (-x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC0 : C ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC2 : C ^ 2 = D₁ * D₂ := by
    have h2 : C ^ 2 * (S.th (-x) * S.th x) = D₁ * D₂ * (S.th (-x) * S.th x) := by
      linear_combination (C * S.th x) * e₁ + (D₁ * S.th x) * e₂
    exact mul_right_cancel₀ (mul_ne_zero hx' hx) h2
  have hCi : C⁻¹ ^ (2 * m) = 1 := by
    rw [inv_pow, pow_mul, hC2, mul_pow, hD₁, hD₂, _root_.one_mul, inv_one]
  obtain ⟨D, hD, e⟩ := hC a
  obtain ⟨k, hk⟩ := hodd
  refine ⟨C⁻¹ ^ m, C⁻¹ ^ (m + 1) * D, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, hCi]
  · rw [mul_pow, hD, _root_.mul_one, ← pow_mul, show (m + 1) * m = 2 * m * (k + 1) by rw [hk]; ring, pow_mul, hCi,
      one_pow]
  · have e' : S.th (-a) = C⁻¹ * D * S.th a := by
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, inv_mul_cancel₀ hC0, _root_.one_mul]
    rw [e', ← _root_.mul_assoc, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, hCi, _root_.one_mul]

end GlobalTheory.ThetaParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFami
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumBC


open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in
set_option maxHeartbeats 1600000 in
theorem refine_factor_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  intro R _ _ _ hCN Q G _ _ P hG hC R' _ _ _ ρ hCN' hρ hfin D ε hRef
  obtain ⟨hPL, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, mi, mp, hip, hpi, hP⟩ := hC
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hR' := admissibleBase_of_completeNormalLocalCharZero hCN'
  have hloc : IsLocalHom ρ := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ρ
      (RingHom.IsIntegral.of_finite hfin) (maximalIdeal R')
    have hc : (maximalIdeal R').comap ρ = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal R').comap ρ := hc.symm ▸ (mem_maximalIdeal a).2 hna
    exact (mem_maximalIdeal _).1 this ha
  obtain ⟨D₁', hD', A₁', U₁', hU, oG₁, oA₁, h₁, h₂⟩ :=
    unif_pull hR hR' ρ hρ (map_maximalIdeal_le ρ) hG' U' F.O F.o oA oG hlin
  obtain ⟨m, o₁, hx, ho⟩ := degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R R' ρ _ _ hD' F.O F.o
  have lin := oLinear_pull R R' _ _ ρ D' D₁' hD' A' A₁' G' _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) U' U₁' hU
    F.O F.o o₁ oA oA₁ oG oG₁ hlin h₁ h₂ hx ho
  obtain ⟨inc', pr', xi, xp, w, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ :=
    _root_.GlobalTheory.FactorPull.pfactor_pull ρ hρ Q D'.toPre F D.toPre ε hRef D₁'.toPre hD' o₁ hx fun a => act_proj _ hD'.e.hom (ho a)
  let F₁ : Factor D.toPre D₁'.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := b₁₀, tau := b₁₁ }
  have alg : F₁.Alg := F.alg
  have ha : ∀ a, oG₁.act a = (Over.pullback (specOf ρ)).map (oG.act a) := fun a =>
    (Category.comp_id _).symm.trans ((h₁ a).trans (Category.id_comp _))
  have gG := isGrpPullback_pullback G (specOf ρ)
  have gG' := (isGrpPullback_pullback G' (specOf ρ)).congr rfl (Category.id_comp _).symm
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁', F₁, alg, A₁', _, _, _, U₁', oA₁, oG₁, (Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Over.pullback (specOf ρ)).map inc, (Over.pullback (specOf ρ)).map pr, _, sqOf gG,
    IsSemiAbelian.pullback _ G' hG', lin, IsSemiAbelian.pullback _ G hG, inferInstance, inferInstance, ?_, ?_, gG,
    isSquare_sqOf gG, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hpi, ha]
  · have hm := lift_sq gG gG' (u := inc) (v := inc ≫ oG.act F.f) (u₁ := (Over.pullback (specOf ρ)).map inc)
      (v₁ := (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f)
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (map_left_fst _ _))
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (by
        rw [ha, ← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _))
    have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
    have H1 : LBIso ((abelian₂ ((Over.pullback (specOf ρ)).obj G') U₁'.LG.L).pull
        (lift (fst _ _ ≫ (Over.pullback (specOf ρ)).map inc) (snd _ _ ≫ (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f) :
          G2 ((Over.pullback (specOf ρ)).obj G) ⟶ G2 ((Over.pullback (specOf ρ)).obj G')).left)
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb (abelian₂ G' U'.LG.L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
    have H2 : LBIso (P.pull (sqOf gG))
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      hP.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl)
    exact LBIso.trans (pull_isLB (DVR.linComb_isLB _ U₁'.LG.isLB _ _) _)
      (pull_isLB (pull_isLB (DVR.linComb_isLB _ U'.LG.isLB _ _) _) _) (pull_isLB hPL _) H1 (LBIso.symm H2)

end GlobalTheory.MumBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section
namespace GlobalTheory.DiagAmpleBC

theorem diag_comp {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) :
    (lift (𝟙 B) (𝟙 B)).left ≫ β₂ = β ≫ (lift (𝟙 A) (𝟙 A)).left := by
  have h1 : (lift (𝟙 B) (𝟙 B)).left ≫ (fst B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : (lift (𝟙 B) (𝟙 B)).left ≫ (snd B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h4 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, h1, Category.assoc, h2, Category.id_comp, Category.comp_id]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, h3, Category.assoc, h4, Category.id_comp, Category.comp_id]

theorem relAmple_diag_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro S T A _ hA P hP hD t B β β₂ hpb hs
  haveI := hA.proper
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [diag_comp A B β β₂ hs] at e₁
  have e := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hpb (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e hD

end GlobalTheory.DiagAmpleBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt GlobalTheory.VB GlobalTheory.GenSmoothCover

namespace GlobalTheory.GenRes

theorem bijective_residueFieldMap {A B : Scheme.{0}} (f : A ⟶ B) [SurjectiveOnStalks f] (x : A) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := A.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨B.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩

theorem residueDegree_eq_one_of_comp {A B C : Scheme.{0}} (g : A ⟶ B) (c : B ⟶ C) (a : A)
    (h : Function.Bijective ((g ≫ c).residueFieldMap a).hom) : c.residueDegree (g a) = 1 := by
  rw [Scheme.residueFieldMap_comp] at h
  have hs : Function.Surjective (c.residueFieldMap (g a)).hom := fun y => by
    obtain ⟨x, hx⟩ := h.2 ((g.residueFieldMap a).hom y)
    exact ⟨x, (g.residueFieldMap a).hom.injective hx⟩
  have hb : Function.Bijective (c.residueFieldMap (g a)).hom := ⟨RingHom.injective _, hs⟩
  letI := (c.residueFieldMap (g a)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  exact (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv).symm.trans
    (Module.finrank_self _)

theorem exists_birational_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsArithVar (ρ ≫ p) d ∧ GenSmooth (ρ ≫ p) d ∧ ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) = 1 := by
  intro hP k _ X _ p D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ‹_›, ρ, hA, fun σ => ?_, ?_, ?_⟩
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have : SurjectiveOnStalks (((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ) := by rw [e]; infer_instance
    rw [← eη]
    exact residueDegree_eq_one_of_comp _ ρ _ (bijective_residueFieldMap _ _)

end GlobalTheory.GenRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetrStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
      (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
      IsSymCoc d.g → ∀ n, d.coc n ∈ symCocycles R (G.A n) :=
  @GlobalTheory.PtExt.coc_mem_symCocycles
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginMemIdealPowOfVanishes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigVan

theorem stalkMap_gs {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (t z) ∈ U)
    (a : Γ(X, U)) : (t.stalkMap z).hom (gs r (t z) U a) = gs (t ≫ r) z U a := by
  rw [gs_eq r (t z) U h, gs_eq (t ≫ r) z U h]
  exact Scheme.Hom.germ_stalkMap_apply t (r ⁻¹ᵁ U) z h _

theorem stalkMap_stalkOf {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (z : Sp S) (v : R) :
    ((Spec.map (CommRingCat.ofHom φ)).stalkMap z).hom (stalkOf ((Spec.map (CommRingCat.ofHom φ)) z) v) =
      stalkOf z (φ v) := by
  have e := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  refine (Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp S).presheaf.germ ⊤ z trivial).hom e.symm

theorem eq_zero_of_stalkOf {S : Type} [CommRing S] (w : S) (h : ∀ z : Sp S, stalkOf z w = 0) : w = 0 := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w = 0 := by
    apply TopCat.Presheaf.section_ext (Sp S).sheaf ⊤
    intro x hx
    exact (h x).trans (map_zero _).symm
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom h1
  simpa using h2

end GlobalTheory.Mum.OrigVan

namespace GlobalTheory.Mum
open OrigVan

theorem origVal_mem_of_vanMod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (α : D.X)
    (b : D.SecB k α) (v : R) (e : ℕ), OrigVal D b v → VanMod I b e → v ∈ I ^ (e + 1) := by
  intro R _ _ I D k α b v e hO hV
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_stalkOf _ fun z => ?_
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (thick R I e z))
  have hG : Good D.P.L (thick R I e z) J := hJ
  have h1 := congrArg ((thick R I e).stalkMap z).hom (hO (thick R I e z) J hG)
  have hm := hG.mem (D.famφB α) (unitW D.P.A)
  have hu : unitW D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w (η[D.P.A])
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ pullback D.P.A.hom (thick R I e) :=
    pullback.lift (thick R I e ≫ unitW D.P.A) (𝟙 _) (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])
  have hs : s ≫ pullback.fst D.P.A.hom (thick R I e) = thick R I e ≫ unitW D.P.A := pullback.lift_fst _ _ _
  have hm' : (s ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈
      LB.wchart D.P.L (D.famφB α) (fun k => J (unitW D.P.A ≫ D.famφB α k)) := by
    rw [hs]; exact hm
  have h0 : ((thick R I e).stalkMap z).hom (sval b (unitW D.P.A) (thick R I e z) J) = 0 := by
    refine (stalkMap_gs (thick R I e) (unitW D.P.A) z _ hm _).trans ?_
    rw [← hs]
    refine (gs_pull s _ z _ hm' _).symm.trans ?_
    refine (congrArg (gs s z _) (hV _)).trans ?_
    refine (gs_eq s z _ hm' _).trans ?_
    rw [map_zero, map_zero]
  rw [h0, map_mul, map_pow, stalkMap_stalkOf] at h1
  exact (((Units.isUnit _).map _).pow k).mul_left_eq_zero.1 h1.symm

end GlobalTheory.Mum
end
end

