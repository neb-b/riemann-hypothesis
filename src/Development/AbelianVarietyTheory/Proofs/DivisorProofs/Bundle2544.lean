module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomOfChart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.BcPull

theorem isom_of_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (L M : MLine p σ)
    (e : M.B.ι → L.B.ι) (hU : ∀ a, M.B.U a ≤ L.B.U (e a))
    (hg : ∀ (x : X) a a', x ∈ M.B.U a → x ∈ M.B.U a' →
      gm (𝟙 X) x (M.B.U a ⊓ M.B.U a') (M.B.g a a') = gm (𝟙 X) x (L.B.U (e a) ⊓ L.B.U (e a')) (L.B.g (e a) (e a')))
    (hφ : ∀ a, ∀ y ∈ ptsIn p σ (M.B.U a), M.φ.φ a y = L.φ.φ (e a) y) : L.Isom M := by
  have le (c : M.B.ι × L.B.ι) : M.B.U c.1 ⊓ L.B.U c.2 ≤ L.B.U (e c.1) ⊓ L.B.U c.2 := inf_le_inf_right _ (hU c.1)
  refine ⟨⟨fun c => res (le c) (L.B.g (e c.1) c.2)⟩, fun c c' => Geo.Tor.unit_ext fun x hx => ?_, fun a b y ha hb => ?_⟩
  · have hx' : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ (M.B.U c'.1 ⊓ L.B.U c'.2) := hx
    refine ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c) hx'.1 _)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (Geo.Tor.gm_div L.B M.B (𝟙 X) x c c' hx')
      ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c') hx'.2 _))).trans ?_)
    have h₁ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) (hU _ hx'.2.1) hx'.2.2
    have h₂ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) hx'.1.2 hx'.2.2
    rw [hg x _ _ hx'.1.1 hx'.2.1, mul_right_comm, h₁, ← h₂, mul_inv_cancel_right]
  · rw [hφ a y ha, L.φ.trans (e a) b y (ptsIn_mono (hU a) ha) hb, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact congrArg (fun z : ℂ => _ + Real.log (‖z‖ ^ 2))
      (CxPts.ev_res (le (a, b)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) _).symm

theorem bc_φ {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    {ρ : k →+* K} (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) (i : PUnit → A.B.ι) (z : CxPts q τ) :
    (A.bc w τ).φ.φ i z = A.φ.φ (i PUnit.unit) (bcPt w τ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * A.φ.φ (i a) (bcPt w τ z)).trans (by simp)

theorem bc_pull_isom : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G Z G' : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (w : j ≫ p = q ≫ spMap ρ) (i : Z ⟶ X) (j' : G' ⟶ Z) (g : G' ⟶ G), g ≫ j = j' ≫ i → ∀ (w' : j' ≫ i ≫ p = (g ≫ q) ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)), ((A.pull i rfl).bc w' τ).Isom ((A.bc w τ).pull g rfl) := by
  intro k K _ _ ρ X G Z G' p q j w i j' g h w' τ A
  have hm (a : PUnit → PUnit → A.B.ι) (x : G') (hx : x ∈ ((A.B.pull j).pull g).U a) :
      x ∈ ((A.B.pull i).pull j').U a := by
    have h₀ : j (g x) ∈ A.B.U (a PUnit.unit PUnit.unit) := Geo.Tor.mem_pull.1 (Geo.Tor.mem_pull.1 hx)
    have h₁ : (g ≫ j) x ∈ A.B.U (a PUnit.unit PUnit.unit) := h₀
    rw [h] at h₁
    exact Geo.Tor.mem_pull.2 (Geo.Tor.mem_pull.2 h₁)
  refine isom_of_chart _ _ (fun a : PUnit → PUnit → A.B.ι => a) hm
    (fun x (a a' : PUnit → PUnit → A.B.ι) ha ha' => ?_) fun (a : PUnit → PUnit → A.B.ι) y _ => ?_
  · refine ((Geo.Tor.gm_pull_g (A.B.pull j) g (𝟙 G') x a a' ha ha').trans
      (Geo.Tor.gm_pull_g A.B j (𝟙 G' ≫ g) x _ _ (Geo.Tor.mem_pull.1 ha) (Geo.Tor.mem_pull.1 ha'))).trans (Eq.symm ?_)
    refine ((Geo.Tor.gm_pull_g (A.B.pull i) j' (𝟙 G') x a a' (hm a x ha) (hm a' x ha')).trans
      (Geo.Tor.gm_pull_g A.B i (𝟙 G' ≫ j') x _ _ (Geo.Tor.mem_pull.1 (hm a x ha))
        (Geo.Tor.mem_pull.1 (hm a' x ha')))).trans ?_
    rw [Category.assoc, Category.assoc, h]
  · refine (((A.bc w τ).φ.pull_φ g rfl a y).trans (bc_φ w τ A _ _)).trans (Eq.symm ?_)
    refine ((bc_φ w' τ (A.pull i rfl) a y).trans (A.φ.pull_φ i rfl _ _)).trans (congrArg _ (Subtype.ext ?_))
    change (y.1 ≫ j') ≫ i = (y.1 ≫ g) ≫ j
    rw [Category.assoc, Category.assoc, h]

end GlobalTheory.Mix.BcPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem kaehler_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens), ∃ (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)) (ω : Fin g → Ω[Sec (str A) U.1⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) ∧ (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) ∧ (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) ∧ (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) ∧ ∀ a ξ, ∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ (Pi.single a 1) = val u.ex U.1 ((d a).liftKaehlerDifferential ξ) z := by
  intro A _ g L u hA U
  obtain ⟨d, hcomm, hval⟩ := _root_.GlobalTheory.CechPer.exists_commuting_coordinate_derivations A g L u hA U.1
  have hsm := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨hfin, hproj, hrk⟩ := _root_.GlobalTheory.CechPer.kaehler_sec_finite_projective_rank A g hsm U
  have hsurj := _root_.GlobalTheory.CechPer.surjective_pi_liftKaehler_coord A g L u hA U d hval
  set Φ : Ω[Sec (str A) U.1⁄ℂ] →ₗ[Sec (str A) U.1] (Fin g → Sec (str A) U.1) :=
    LinearMap.pi fun a => (d a).liftKaehlerDifferential with hΦ
  have hinj : Function.Injective Φ := _root_.GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq _ _ g Φ hfin hproj hrk hsurj
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦa : ∀ ξ a, Φ ξ a = (d a).liftKaehlerDifferential ξ := fun ξ a => rfl
  refine ⟨d, fun b => e.symm (Pi.single b 1), hcomm, hval, ?_, ?_, ?_⟩
  · intro a b
    rw [← hΦa]
    have : Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := e.apply_symm_apply _
    rw [this, Pi.single_apply]
  · intro ξ
    apply hinj
    funext c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]
    have h1 : ∀ b, Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := fun b => e.apply_symm_apply _
    simp only [h1]
    rw [Finset.sum_eq_single c (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero])
      (fun h => absurd (Finset.mem_univ c) h), Pi.single_eq_same, hΦa]
    exact (_root_.mul_one _).symm
  · intro a ξ z hz
    obtain ⟨ev, hev⟩ := (_root_.GlobalTheory.CechPer.pre_val_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
    obtain ⟨_, hsm', hD⟩ := _root_.GlobalTheory.CechPer.evForm_rules A g L u U.1 z hz
    have hmem : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have hev' : ∀ b : Sec (str A) U.1, val u.ex U.1 b z = ev b := hev
    suffices h : evForm u.ex U.1 z ξ (Pi.single a 1) = ev ((d a).liftKaehlerDifferential ξ) from
      h.trans (hev' _).symm
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [hD, Derivation.liftKaehlerDifferential_comp_D]
      exact (hval a y z hz).symm.trans (hev' _)
    | zero => simp only [map_zero, ContinuousLinearMap.zero_apply]
    | add x y _ _ hx hy => simp only [map_add (f := _), ContinuousLinearMap.add_apply, hx, hy]
    | smul r x _ hx =>
      rw [hsm', ContinuousLinearMap.smul_apply, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul, hev' r]

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem Trait.exists_lift {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (F : Type) [Field F] [Algebra (FractionRing W) F] (z : Sp F ⟶ C.G.left)
    (hz : z ≫ C.G.hom = jFK (R := W) F ≫ jK W ≫ T.ξ) :
    ∃ x : TFK (R := W) F ⟶ T.A.A, x.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z := by
  have w₁ : z ≫ C.G.hom = (jFK (R := W) F ≫ jK W) ≫ T.ξ := by rw [hz, Category.assoc]
  have w₂ : T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁ ≫ T.G.hom = jFK (R := W) F ≫ jK W :=
    T.cart.1.lift_snd _ _ _
  let g₂ : Sp F ⟶ pullback T.G.hom (jK W) := pullback.lift (T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁) (jFK (R := W) F) w₂
  have hs : T.U.gen.hom.left ≫ T.A.A.hom = pullback.snd T.G.hom (jK W) := Over.w T.U.gen.hom
  have hgi : T.U.gen.hom.left ≫ T.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨Over.homMk (g₂ ≫ T.U.gen.hom.left) (by
    show (g₂ ≫ T.U.gen.hom.left) ≫ T.A.A.hom = jFK (R := W) F
    rw [Category.assoc, hs]
    exact pullback.lift_snd _ _ _), ?_⟩
  show (g₂ ≫ T.U.gen.hom.left) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z
  rw [Category.assoc, reassoc_of% hgi, pullback.lift_fst_assoc]
  exact T.cart.1.lift_fst _ _ _

end GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

theorem labExt_of_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], Nonempty (Trait C W) →
    ∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ (C.lab j) (C.lab j) := by
  intro R _ _ _ hR D C j W _ _ _ ⟨T⟩ σ p q hpq
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap T.inj)).toAlgebra
  have cF : Compat T.φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap T.inj r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) (Kb W)
  obtain ⟨r, hr⟩ := exists_ext hB em q
  have hr' : QkExt (em.comp σ).toRingHom p r := qkExt_trans hpq hr
  have hr₁ := isPullGtF_pullGt T.hD hGF cF r.g

  have hgp : jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ = jFK (R := R) (Kb W) ≫ C.gp := by
    let ρ : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp T.φ)
    have hρ : Function.Injective ρ :=
      (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
    have hy : (jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ) ≫ C.π = spMap ρ := by
      rw [Category.assoc, Category.assoc, T.ξ_π, spMap_comp, spMap_comp]
    obtain ⟨ga, hga, e⟩ := Modif.factor_gp R C.toModif (Kb W) ρ _ hρ hy
    have hga' : ga = algebraMap (FractionRing R) (Kb W) :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun s => (hga s).trans (cF s).symm)
    rw [e, hga']
  have hz : ∀ (τ : Kb R →ₐ[FractionRing R] Kb W) (x : TFK (R := R) (Kb R) ⟶ C.A.A),
      (spMap τ.toRingHom ≫ x.left ≫ C.α) ≫ C.G.hom = jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ := by
    intro τ x
    rw [hgp, Category.assoc, Category.assoc, C.α_cart.1.w, ← Category.assoc x.left, Over.w x, ← Category.assoc]
    show (spMap τ.toRingHom ≫ spMap (algebraMap (FractionRing R) (Kb R))) ≫ C.gp = _
    rw [← spMap_comp]; exact congrArg (fun f => spMap f ≫ C.gp) τ.comp_algebraMap
  obtain ⟨x₁, hx₁⟩ := T.exists_lift (Kb W) _ (hz em (C.lab j q))
  obtain ⟨x₂, hx₂⟩ := T.exists_lift (Kb W) _ (hz (em.comp σ) (C.lab j p))
  have t₁ := T.lab (Kb W) em cF j q r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₁ hr rfl hr₁ hx₁
  have t₂ := T.lab (Kb W) (em.comp σ) cF j p r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₂ hr' rfl hr₁ hx₂
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ bW T.D' T.A T.G hGs T.U (Kb W) (C.n ^ j) hk
  have e : x₁ = x₂ := ((hf.1 _ _).1 t₁).trans ((hf.1 _ _).1 t₂).symm
  subst e
  have e' := hx₁.symm.trans hx₂
  haveI : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (spMap em.toRingHom)).1 (C.α_cart.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, e', Category.assoc, ← Category.assoc (spMap em.toRingHom), ← spMap_comp]
    rfl
  · rw [Category.assoc, Over.w (C.lab j q), Category.assoc, Category.assoc, Over.w (C.lab j p)]
    exact congrArg (spMap em.toRingHom ≫ ·) ((spMap_comp _ _).symm.trans (congrArg spMap σ.comp_algebraMap)).symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
namespace GlobalTheory.LabelTransfer

theorem isAlgebraic_padicAlgCl (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V)
    [Algebra (FractionRing V) (PadicAlgCl p)]
    (hV : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    Algebra.IsAlgebraic (FractionRing V) (PadicAlgCl p) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨P, hP0, hPz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) z
  set κ := algebraMap (FractionRing V) (PadicAlgCl p)
  have hl : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) ∈ Polynomial.lifts κ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV _
  obtain ⟨P', hP'⟩ := hl
  rw [Polynomial.coe_mapRingHom] at hP'
  refine ⟨P', fun h => hP0 ?_, ?_⟩
  · have : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) = 0 := by rw [← hP', h, Polynomial.map_zero]
    exact (Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).1 this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval z (P'.map κ) = 0
    rw [hP', ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hPz]

end GlobalTheory.LabelTransfer

namespace GlobalTheory.LabelTransfer

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  intro o Ω _ _ _ S ρ p _ y₀ u eA s H F _ _ _ k hk _ q q' a a' hq hq' haa
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : Algebra.IsAlgebraic (FractionRing u.V) (PadicAlgCl p) :=
    isAlgebraic_padicAlgCl p u.V u.complete u.norm_le
  let emb : PadicAlgCl p →ₐ[FractionRing u.V] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (PadicAlgCl p) F := emb.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing u.V) (PadicAlgCl p) F :=
    IsScalarTower.of_algebraMap_eq fun c => (emb.commutes c).symm
  have hf : (algebraMap (PadicAlgCl p) F).comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) =
      algebraMap (FractionRing u.V) F := (IsScalarTower.algebraMap_eq _ _ _).symm
  have hk0 : ((k : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q
  obtain ⟨q₀', hq₀'⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q'
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) k hk
  obtain ⟨f₁, hf₁, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U F k hk
  have hL := GlobalTheory.firstFiveLaws
  have e₁ : QkToAkU u.U.toUnifPre F k q (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀) :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀ _).1 ((hf₀ _ _).2 rfl)
  have e₂ : QkToAkU u.U.toUnifPre F k q' (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀') :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀' _).1 ((hf₀ _ _).2 rfl)
  have ha : a = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀ :=
    ((hf₁ _ _).1 hq).trans ((hf₁ _ _).1 e₁).symm
  have ha' : a' = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀' :=
    ((hf₁ _ _).1 hq').trans ((hf₁ _ _).1 e₂).symm
  have hepi : Epi (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left := by
    have : Flat (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    have : Surjective (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      ⟨fun z => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _⟩⟩
    have : QuasiCompact (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    exact Flat.epi_of_flat_of_surjective _
  have hx : (f₀ q₀).left = (f₀ q₀').left ≫ eA.left := by
    rw [ha, ha', Over.comp_left, Over.comp_left, Category.assoc] at haa
    exact (cancel_epi _).1 haa
  have := H k q₀' q₀ (f₀ q₀') (f₀ q₀) hk ((hf₀ _ _).2 rfl) ((hf₀ _ _).2 rfl) hx
  rw [hq₀.1, hq₀'.1]
  exact this

end GlobalTheory.LabelTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AllEmb

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

theorem lab_indep_level {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (hB : D.TauBimult) {A : PolAV (Sp (FractionRing R))} {lab : Labels D A}
    (hlab : ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D (Kb R) k), QkExt σ.toRingHom p p' →
      (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left)
    (τ₁ τ₂ : Kb R →ₐ[FractionRing R] F) {p q : QkPt D (Kb R) k} {r : QkPt D F k}
    (h₁ : QkExt τ₁.toRingHom p r) (h₂ : QkExt τ₂.toRingHom q r) :
    spMap τ₁.toRingHom ≫ (lab k p).left = spMap τ₂.toRingHom ≫ (lab k q).left := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Kb R →ₐ[FractionRing R] Kb R, τ₂.toRingHom.comp σ.toRingHom = τ₁.toRingHom := by
    letI : Algebra (Kb R) F := τ₂.toRingHom.toAlgebra
    haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (τ₂.commutes x).symm
    exact ⟨τ₁.restrictNormal (Kb R), RingHom.ext fun x => τ₁.restrictNormal_commutes (Kb R) x⟩
  obtain ⟨q', hq'⟩ := exists_ext hB σ p
  obtain ⟨r', hr'⟩ := exists_ext hB τ₂ q'
  have h₃ := qkExt_trans hq' hr'
  rw [hσ] at h₃
  obtain rfl := ext_unique hB τ₁ h₁ h₃
  obtain rfl := qkExt_inj hB τ₂ h₂ hr'
  rw [hlab σ p q hq', ← Category.assoc, ← Geo.Tor.spMap_comp, hσ]

theorem induces_of_one_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn _ _ hlab W _ _ _ hW φ iφ _ G' _ _ D' A' U' a hG ⟨ga, hga, gpa, _⟩ hD j
    ⟨C, _, _, _, _, emC, cC, HC⟩ F _ _ _ _ em cF p p₁ p' x' y₁ y₂ y₃ y₄
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  have := hR.2
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have cK : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨e⟩ := nonempty_lift (FractionRing R) (Kb W)

  have fac : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      algebraMap (FractionRing R) L = (algebraMap (FractionRing W) L).comp ga := fun L _ _ _ c =>
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c r).trans
      (congrArg (algebraMap (FractionRing W) L) (hga r).symm))
  have up : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      ∀ i : Kb W →ₐ[FractionRing W] L, ∃ i' : Kb W →ₐ[FractionRing R] L, i'.toRingHom = i.toRingHom := fun L _ _ _ c i =>
    ⟨⟨i.toRingHom, fun t => by rw [fac L c]; exact i.commutes (ga t)⟩, rfl⟩

  have key : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L],
      Compat φ L → ∀ (i : Kb W →ₐ[FractionRing W] L) (m : Kb R →ₐ[FractionRing R] L)
      (q : QkPt D.toPre (Kb R) (n ^ j)) (q₁ : QkPt D.toPre (Kb W) (n ^ j)) (x₀ : TFK (R := W) (Kb W) ⟶ A'.A),
      QkExt e.toRingHom q q₁ → x₀.left ≫ a = spMap e.toRingHom ≫ (lab (n ^ j) q).left →
      ∀ (s : QkPt D.toPre (Kb R) (n ^ j)) (s₁ : QkPt D.toPre L (n ^ j)) (s' : QkPt D'.toPre L (n ^ j))
        (z : TFK (R := W) L ⟶ A'.A), QkExt i.toRingHom q₁ s₁ → QkExt m.toRingHom s s₁ → s'.y = hD.xe.symm s₁.y →
        IsPullGtF φ hD L s₁.g s'.g → z.left ≫ a = spMap m.toRingHom ≫ (lab (n ^ j) s).left →
        (QkToAkU U'.toUnifPre (Kb W) (n ^ j) (pullQk hD hGF cK hB hB' q₁) x₀ ↔ QkToAkU U'.toUnifPre L (n ^ j) s' z) := by
    intro L _ _ _ _ c i m q q₁ x₀ hq hx₀ s s₁ s' z w₀ w₁ w₂ w₃ w₄
    obtain ⟨i', hi'⟩ := up L c i
    obtain ⟨⟨t, ht⟩, -, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG U' _ L i (n ^ j) hk
      (pullQk hD hGF cK hB hB' q₁)
    have t₁ : IsPullGtF φ hD L s₁.g t.g :=
      isPullGtF_ext hD c i.toRingHom i.comp_algebraMap (isPullGtF_pullGt hD hGF cK _) w₀ ht
    have t₂ : t.y = hD.xe.symm s₁.y := by rw [ht.1, w₀.1]; rfl
    obtain rfl : s' = t := ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨w₂, w₃⟩).trans
      ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨t₂, t₁⟩).symm
    have u : QkExt (i'.comp e).toRingHom q s₁ := by
      have := qkExt_trans hq w₀
      rw [← hi'] at this
      exact this
    have l := lab_indep_level hB (fun σ => hlab σ j) m (i'.comp e) w₁ u
    refine hgal s' x₀ z ht ?_
    apply gpa.1.hom_ext
    · rw [w₄, Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp, l, ← hi']
      rfl
    · rw [Category.assoc, Over.w z, Over.w x₀]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap i.comp_algebraMap)).symm
  obtain ⟨i⟩ := nonempty_lift (FractionRing W) F
  obtain ⟨i₀⟩ := nonempty_lift (FractionRing W) C
  obtain ⟨i', hi'⟩ := up F cF i
  obtain ⟨i₀', hi₀'⟩ := up C cC i₀
  obtain ⟨q₁, hq₁⟩ := exists_of_ext hB i' hk p₁
  obtain ⟨q, hq⟩ := exists_of_ext hB e hk q₁
  obtain ⟨x₀, hx₀⟩ := exists_lift_pt gpa.1 e.toRingHom e.comp_algebraMap (lab (n ^ j) q)
  obtain ⟨r₁, hr₁⟩ := exists_ext hB i₀' q₁
  obtain ⟨r, hr⟩ := exists_of_ext hB emC hk r₁
  obtain ⟨z, hz⟩ := exists_lift_pt gpa.1 emC.toRingHom (emC.comp_algebraMap.trans (fac C cC)) (lab (n ^ j) r)
  have hC := HC r r₁ (pullQk hD hGF cC hB hB' r₁) z hr rfl (isPullGtF_pullGt hD hGF cC _) hz
  exact (key F cF i em q q₁ x₀ hq hx₀ p p₁ p' x' (hi' ▸ hq₁) y₁ y₂ y₃ y₄).1
    ((key C cC i₀ emC q q₁ x₀ hq hx₀ r r₁ _ z (hi₀' ▸ hr₁) hr rfl (isPullGtF_pullGt hD hGF cC _) hz).2 hC)

end GlobalTheory.Mum.AllEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ X), x ≫ (π ≫ sY) = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ sY = spMap β → ∀ v : epsPtR x ⟶ A₀, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A₀), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) := by
  first | (exact @GlobalTheory.LieGalDesc.lie_descends) | (exact GlobalTheory.LieGalDesc.lie_descends) | (intros; apply GlobalTheory.LieGalDesc.lie_descends  <;> assumption)
end

