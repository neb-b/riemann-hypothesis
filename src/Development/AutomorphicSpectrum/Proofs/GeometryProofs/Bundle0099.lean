module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoBaseChange
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tate_iso_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (i : k →+* k') (x : Sp k ⟶ X), IsProper (pullback.snd t.G.hom x) → ∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t (spMap i ≫ x), ∀ n, 0 < n → (I'.ζ n : k') = i (I.ζ n) ∧ ∀ a, (I'.ev n a).left = spMap i ≫ (I.ev n a).left := by
  intro E _ _ _ H D X t k k' _ _ _ _ _ i x hprop I
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨_, _, -⟩ := PositivityTheory.HtPt.Mg.finrank_La D
  let e := PositivityTheory.HtPt.Mg.extPt i x
  have hprop' : IsProper (pullback.snd t.G.hom (spMap i ≫ x)) :=
    PositivityTheory.HtPt.Mg.proper_of_hom (A := t.G) e hprop
  have hone : ∀ g : Over.mk x ⟶ t.G, e ≫ g = 1 ↔ g = 1 := by
    intro g
    constructor
    · intro h
      exact PositivityTheory.HtPt.Mg.extPt_inj i x (h.trans (MonObj.comp_one e).symm)
    · intro h
      rw [h, MonObj.comp_one]
  have hfinT : ∀ n, 0 < n → Finite {y : Over.mk x ⟶ t.G // y ^ n = 1} := by
    intro n hn
    let N : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • (LinearMap.id : D.La →ₗ[ℤ] D.La))
    haveI : Finite (D.La ⧸ N) := Module.finite_of_fg_torsion _ (by
      intro q
      refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
      induction q using Submodule.Quotient.induction_on with
      | H a =>
        show (n : ℤ) • (Submodule.Quotient.mk a : D.La ⧸ N) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact ⟨a, rfl⟩)
    have hex : ∀ y : {y : Over.mk x ⟶ t.G // y ^ n = 1}, ∃ a, I.ev n a = y.1 :=
      fun y => (I.onto n hn y.1).1 y.2
    refine Finite.of_injective (fun y => (Submodule.Quotient.mk (hex y).choose : D.La ⧸ N)) ?_
    intro y y' hyy
    have h1 := (hex y).choose_spec
    have h2 := (hex y').choose_spec
    rw [Submodule.Quotient.eq] at hyy
    obtain ⟨c, hc⟩ := hyy
    apply Subtype.ext
    rw [← h1, ← h2]
    have hsm : ((n : ℤ) • LinearMap.id : D.La →ₗ[ℤ] D.La) c = n • c := by
      simp [natCast_zsmul]
    have hdec : (hex y).choose = (hex y').choose + n • c := by
      rw [← hsm, hc]
      abel
    rw [hdec, I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map (i : k →* k') (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective i.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n a => e ≫ I.ev n a
            add := fun n a b => by simp only [I.add, MonObj.comp_mul]
            lin := fun n c a => by simp only [I.lin, Category.assoc]
            ker := fun n hn a => by rw [← I.ker n hn a]; exact hone _
            onto := fun n hn g => by
              constructor
              · intro hg
                obtain ⟨y, hy, rfl⟩ := PositivityTheory.HtPt.Mg.torsion_desc t.G i x n (hfinT n hn) g hg
                obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
                exact ⟨a, rfl⟩
              · rintro ⟨a, rfl⟩
                rw [← MonObj.comp_pow, (I.onto n hn _).2 ⟨a, rfl⟩, MonObj.comp_one]
            tower := fun n m hn hm a => by rw [← MonObj.comp_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              have h := PositivityTheory.HtPt.Mg.weilIs_pull_of_proper t.semi t.PP.isLB hprop' e (I.isom n hn a b)
              show Out.WeilIs t.G t.PP.L (n : ℤ) (e ≫ I.ev n a) (e ≫ I.ev n b)
                (unitOn ((Units.map (i : k →* k') (I.ζ n)) ^ D.EF a b))
              have hm : (Units.map (i : k →* k') (I.ζ n)) ^ D.EF a b
                  = Units.map (i : k →* k') (I.ζ n ^ D.EF a b) := by
                simp [map_zpow, map_pow]
              rw [hm]
              convert h using 1
              exact (PositivityTheory.HtPt.Mg.unitOn_map i _).symm }, ?_⟩
  intro n hn
  exact ⟨rfl, fun a => rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c)
    (h' : genPt ξ ⤳ c') (s : X.presheaf.stalk c) :
    genMap ξ ⟨c', h'⟩ (X.presheaf.stalkSpecializes (specializes_of_eq hc) s) = genMap ξ ⟨c, h⟩ s := by
  subst hc
  simp [TopCat.Presheaf.stalkSpecializes_refl]

theorem closedPoint_specMap_fromSpecStalk {R : CommRingCat.{0}} [IsLocalRing R] (x : X)
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem stalkSpecializes_comp_comp_eq_of_eq {x y : X} (h1 : x ⤳ y) (h2 : y ⤳ x) (hxy : x = y)
    {R : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ R) :
    X.presheaf.stalkSpecializes h2 ≫ X.presheaf.stalkSpecializes h1 ≫ g = g := by
  subst hxy
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem stalkSpecializes_stalkClosedPointTo {K : Type} [Field K] (x : X)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ.hom]
    (hc : (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint (CommRingCat.of K)) = x) :
    X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = φ := by
  have key := (SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩
  obtain ⟨h, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  rw [show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2,
    TopCat.Presheaf.stalkCongr_hom]
  exact stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ

private theorem isLocalHom_of_field' {K K' : Type} [Field K] [Field K'] (f : K →+* K') : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩

theorem valAt_of_field_map {K K' : Type} [Field K] [Field K'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (w : Spec (CommRingCat.of K) ⟶ X) (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K')
    (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') {a : Ω} {u : K} (hv : ValAt ξ w a u) :
    ValAt ξ w' a (f u) := by
  obtain ⟨h, s, hs, hr⟩ := hv
  subst e
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K',
      ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := ⟨_, rfl⟩
  haveI : IsLocalHom ψ.hom := by
    haveI := isLocalHom_of_field' f
    have hh : ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom := by
      subst hψ
      rfl
    rw [hh]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom (isLocalHom_of_field' f)
      (Scheme.isLocalHom_stalkClosedPointTo w)
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
  have hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w) := by
    rw [hψ]
    erw [Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm
  rw [hw']
  have hc := closedPoint_specMap_fromSpecStalk (centre w) ψ
  have hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w := hc
  have h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) := by
    rw [hc']
    exact h
  refine ⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩
  · exact (genMap_stalkSpecializes ξ hc' h h' s).trans hs
  · have H3 := stalkSpecializes_stalkClosedPointTo (centre w) ψ hc
    have H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
        Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s :=
      congrArg (fun g => g.hom s) H3
    have hψs : ψ.hom s = f u := by
      rw [← hr]
      subst hψ
      rfl
    exact H.trans hψs

theorem valAt_complex : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  intro X Ω _ ξ L _ _ z σ a u hv
  exact valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv

end GlobalTheory.CompanionTheory.Ar.RootHt.PullVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompare
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.UnitHt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv_section {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]


omit [∀ k, Fintype (ι k)] in
theorem ptHt_neg (a : K → ℤ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, ι k) → L) :
    ptHt (fun k => (((-a) k : ℤ) : ℝ)) (fun z => -φ z) L w = -ptHt (fun k => (a k : ℝ)) φ L w := by
  have e : ∀ v : FinitePlace L, ∑ k, (((-a) k : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) =
      (-1 : ℝ) • ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  simp only [ptHt, e]
  rw [← smul_finsum, Finset.sum_neg_distrib, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Ht.UnitHt


open GlobalTheory.CompanionTheory.Ar.Ht.UnitHt in
theorem GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  intro K _ ι _ Ω _ y d hAr hB a u c hV φ L _ _ w hw val hv hval
  obtain ⟨hu, q, m, hq, hm, hlog, h1, h2⟩ := hV
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : Real.log m / q ≤ c := by
    rw [div_le_iff₀ hq']
    linarith
  have b₁ := SecLow.height_ge_of_section K ι Ω y d hAr hB a u q m hq hm h1 φ L w hw val hv hval
  have b₂ := SecLow.height_ge_of_section K ι Ω y d hAr hB (-a) u⁻¹ q m hq hm h2 (fun z => -φ z) L w hw val⁻¹
    (inv_ne_zero hv) (UnitHt.hasVal_inv_section hu hw hv hval)
  rw [UnitHt.ptHt_neg] at b₂
  have e : ∑ σ : L →+* ℂ, (-φ (fun p => σ (w p)) - Real.log ‖σ val⁻¹‖) =
      -∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_inv₀, norm_inv, Real.log_inv]
    ring
  rw [e, mul_neg] at b₂
  rw [abs_le]
  constructor <;> linarith
end

