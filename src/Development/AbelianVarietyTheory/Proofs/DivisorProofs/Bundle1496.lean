module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_polAV_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S X : Scheme.{0}} {t : SAB H S} {u : SAB H X} {x : S ⟶ X} (m : SABMap t u x) (hp : IsProper u.G.hom)
    (ha : RelAmple u.G u.PP.L) (hk : KTriv u.G u.PP.L) {C : Type} [Field C] (y : Sp C ⟶ S) :
    letI := H.starRing
    ∃ (A : PolAV (Sp C)) (oA : A.OAct (𝓞 E)) (φ : A.A.left ⟶ t.G.left), IsGrpPullback A.A t.G y φ ∧
      (∀ a, (oA.act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧ LBIso A.L (u.PP.L.pull (φ ≫ m.φ)) := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull y t
  generalize (⟨(Over.pullback y).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨w, g, -⟩ := n.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (y ≫ x) (IsLocalRing.closedPoint C)) trivial
  have hy : ∀ z, (y ≫ x) z ∈ U := fun z =>
    (congrArg (fun V => z ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem (y ≫ x) hc)).mpr trivial
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hp
  have hA' := relAmple_pull n.cart.1 u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy ha
  have hK' := kTriv_pull n.cart u.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hk
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hL : LBIso t'.PP.L (u.PP.L.pull (m₁.φ ≫ m.φ)) := hn ▸ ⟨w, g⟩
  exact ⟨GenericPol.toPolAV t' d hd hp' hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, m₁.φ, m₁.cart,
    m₁.act, hL⟩

theorem exists_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → v.Integers O → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O), (∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) → ∃ (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ hpO _ _ _ _ inst hstar hv T io y₀ hy k kO hk
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨G, t', m₁, m₂, -⟩ := y₀.2.2
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  have hinj : Function.Injective ((algebraMap O C).comp kO) := fun a b h => by
    simp only [RingHom.comp_apply, hk] at h
    exact IsFractionRing.injective T.V T.Fr (k.injective h)
  have hp0 : ∀ {R : Type} [CommRing R] (f : R →+* O), (p : R) ≠ 0 := fun f h =>
    (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero : (p : C) ≠ 0) (by
      rw [← map_natCast ((algebraMap O C).comp f), h, map_zero])
  have hpu : ∀ {R : Type} [CommRing R] (f : R →+* O), ¬ IsUnit (p : R) := fun f h =>
    hpO.out (by simpa using h.map f)
  haveI : IsLocalHom kO := ⟨fun a ha => by
    by_contra hau
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact not_isUnit_zero ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hu
      exact hau (hu ▸ u.isUnit)
    rw [hu, map_mul, map_pow] at ha
    have h1 : IsUnit (kO ϖ) := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
    obtain ⟨n', u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 kO) hϖ
    refine hpO.out ?_
    rw [← map_natCast kO, hu', map_mul, map_pow]
    exact (u'.isUnit.map kO).mul (h1.pow _)⟩
  obtain ⟨T', φ', G', m, hi, hf, -, -, U, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  obtain ⟨f', -, hf'⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ' hi hf.to_isIntegral kO hinj
  have hI : ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal T'.V ^ n, f' a ∈ Ideal.span {(p : O)} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hp0 f') hϖ
    refine ⟨n, fun a ha => ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨f' (b * ↑u⁻¹), ?_⟩
    rw [← map_natCast f', ← map_mul, hu, _root_.mul_assoc, Units.inv_mul_cancel_left]
  obtain ⟨A, oA, φ, hφ, hφa, hL⟩ :=
    exists_polAV_fibre m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (spMap k)
  have e1 : spMap f' ≫ spMap φ' = spMap kO := by rw [spMap_spMap, hf']
  have e2 : spMap k ≫ spMap (algebraMap T.V T.Fr) = spMap ((algebraMap O C).comp f') ≫ spMap φ' := by
    rw [spMap_spMap, spMap_spMap, RingHom.comp_assoc, hf']
    exact congrArg _ (RingHom.ext fun a => (hk a).symm)
  have h2 : IsGrpPullback A.A G.G (spMap ((algebraMap O C).comp f') ≫ spMap φ') (φ ≫ m₂.φ) :=
    (hφ.comp m₂.cart).congr e2 rfl
  obtain ⟨j, hj1, hj2⟩ : ∃ j : A.A.left ⟶ G'.G.left, j ≫ m.φ = φ ≫ m₂.φ ∧
      j ≫ G'.G.hom = A.A.hom ≫ spMap ((algebraMap O C).comp f') :=
    ⟨m.cart.1.lift _ _ (h2.1.w.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩
  have hj : IsGrpPullback A.A G'.G (spMap ((algebraMap O C).comp f')) j :=
    m.cart.cancel (h2.congr rfl hj1.symm) hj2
  have hja : ∀ a, (oA.act a).left ≫ j = j ≫ (G'.act.toRingAct.act a).left := fun a => m.cart.1.hom_ext
    (by
      change _ = (j ≫ (G'.act.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, m.act, hj1, reassoc_of% hj1, reassoc_of% (hφa a), m₂.act])
    (by rw [Category.assoc, Category.assoc, Over.w, hj2, Over.w_assoc])
  obtain ⟨ε⟩ : Nonempty (Eps p C) := inferInstance
  obtain ⟨-, -, -, -, -, P, -, -, -, -, hA, -, -, -, -, π, -, hπ, -, -, -, hgen, hπa, -⟩ :=
    exists_point_of_unif U.U.toUnifPre G'.semi U.lin hv ε f' hI A oA j hj hja
  clear hja hφa hj
  clear oA
  subst hA
  refine ⟨P, φ ≫ m₁.φ, hk, G, t', m₁, m₂, π ≫ m.φ, φ, (hπ.comp m.cart).congr e1 rfl, fun a => ?_, hφ, ?_, rfl, hL⟩
  · rw [← Category.assoc, hπa, Category.assoc, Category.assoc]
    exact congrArg (π ≫ ·) (m.act a)
  · rw [← Category.assoc, eq_of_heq hgen, hj1]

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrame
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.CongrOrbit


set_option maxHeartbeats 4000000 in
theorem exists_congr_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx
  have hx' : lact γ x ∈ (U.X k).dom := dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)

  let b₁ : Frame (U.X k).Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hm₁ : ∀ τ, mat b₁ τ = 1 := fun τ => rfl
  have hb₁ : b₁ ∈ Bor (U.X k).Ψ r := fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by
    have := hm₁ τ
    change Matrix.of (b₁ τ) = 1 at this
    have h2 := congrFun (congrFun this a) c
    simpa [Matrix.one_apply_ne (ne_of_gt hca)] using h2⟩
  have hrm : rmul (lact γ x) b₁ = lact γ x := by
    funext τ
    change mat (lact γ x) τ * mat b₁ τ = lact γ x τ
    rw [hm₁, Matrix.mul_one]
    rfl
  obtain ⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩) :=
    (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩
  obtain ⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k ⟨lact γ x, hx'⟩
  have hu : F.u (ik k) P' = F.u (ik k) P := by rw [← hPx, ← hPx', hB.1]
  obtain ⟨h, gam, hex, hh, hiso, hM, -⟩ := _root_.GlobalTheory.familyUnif_exp_unique E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu

  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := F.t_surj (ik k) b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'

  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ)
      (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)
    have d0 := hv' τ i
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  let gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := (φ k).symm ≪≫ₗ gam ≪≫ₗ φ k
  let A : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ i j =>
    if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0
  have hA0 : ∀ τ i j, j < i → A τ i j = 0 := by
    intro τ i j hji
    simp only [A]
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  have hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
        ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j := by
    intro τ i hi v
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP', Equiv.apply_symm_apply]
    simp only [A]
    rw [dite_eq_left ⟨hi, j.2⟩]
    rfl
  have hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E)
      (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E)) := by
    intro u v
    obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]

  obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso
  have hε : ε = 1 := mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)
  have hUS : IsUStab (U.X k).Gm (U.X k).Λ η := ⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩
  have hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ,
      (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y := by
    intro w hw
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨w, hw⟩
    obtain ⟨e₀, he₀⟩ := f₁ a
    refine ⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩
    have h1 := hav ⟨w, hw⟩
    have h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀ := by
      simp only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add (f := _), map_nsmul]
    rw [h2] at h1
    change (η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1
    rw [h1]
    simp [Nat.cast_smul_eq_nsmul]

  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  let ρe := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ := ρe.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j :=
    fun τ i hi v hv => by
      have := hAr (ρe.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  obtain ⟨b, hb, hxb, -⟩ := _root_.GlobalTheory.PeriodBorel.borel_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS)
    (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ))
    (fun τ => hA0 _) hrel
  exact ⟨η, hUS, hcong, b, hb, hxb⟩

end GlobalTheory.CongrOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealIdeleFlow
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_real_idele_flow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ l : ℝ → (AF F ⊗[F] E)ˣ, Continuous l ∧ (∀ s t, l (s + t) = l s * l t) ∧
      (∀ t, sigR (AF F) σ (l t).1 = (l t).1) ∧ ∀ t, (absE F E (l t) : ℝ) = Real.exp t := by
  have := h.1
  let e := fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  have hρ : Continuous ρ := (continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const
  have hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖ := fun w x =>
    (e w).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x
  let ι : AF F →* AF F ⊗[F] E := (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom
  have hι : Continuous ι := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let d : ℕ := Fintype.card (InfinitePlace F)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let u : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)
  have hu : Continuous u := Units.continuous_iff.2
    ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop,
      show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from
        Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩
  refine ⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_,
    fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩
  · rw [← map_mul]
    exact congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))
  · have h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2 := by
      change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _
      haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
    have h2 : ∀ v, evFin F v (ρ (u t)) = 1 := fun v => rfl
    have h3 : ∀ w : InfinitePlace F, w.mult = 1 := fun w => if_pos (IsTotallyReal.isReal w)
    simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3,
      one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn,
      Finset.prod_const, Finset.card_univ]
    change (‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ResLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.TanVec

theorem exists_coords_derivs {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      ∀ a c, d c (x a) = if a = c then 1 else 0 := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

def jetHom {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (d : A →+ A)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a) : A →+* DualNumber K where
  toFun s := (φ s, φ (d s))
  map_one' := by
    have h1 : d 1 = 0 := by
      have := hd 1 1
      simpa using this
    refine TrivSqZeroExt.ext (map_one φ) ?_
    change φ (d 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    change φ (d 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    change φ (d (s + t)) = φ (d s) + φ (d t)
    rw [map_add (f := _), map_add (f := _)]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change φ (d (s * t)) = φ s * φ (d t) + φ (d s) * φ t
    rw [hd, map_add (f := _), map_mul, map_mul, mul_comm (φ t)]

theorem exists_tangent_matrix : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] {K : Type} [Field K] (z : Sp K ⟶ Y), ∃ (O : Y.Opens) (_ : ⊤ ≤ z ⁻¹ᵁ O) (x : Fin D → Γ(Y, O)) (w : Fin D → (Sp (DualNumber K) ⟶ Y)), (∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z) ∧ ∀ hwO : (∀ b, ⊤ ≤ w b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (x a)).snd).det ≠ 0 := by
  intro k _ Y p D _ K _ z
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd⟩ := exists_coords_derivs h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  choose w hw he using fun c => exists_evalPt_eq hO (jetHom (evalPt z _ hzO) (d c) (hl c))
  refine ⟨_, hzO, x, w, fun b => ?_, fun hwO => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw b (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ (w b) _ (hw b) h' f).trans ?_
    rw [he]
    rfl
  · have hm : (Matrix.of fun a b => (evalPt (w b) _ (hwO b) (x a)).snd) = (1 : Matrix (Fin D) (Fin D) K) := by
      ext a b
      have e1 : (evalPt (w b) _ (hwO b) (x a)).snd = evalPt z _ hzO (d b (x a)) := by
        rw [he]
        rfl
      rw [Matrix.of_apply, e1, hd, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, Matrix.det_one]
    exact one_ne_zero

end GlobalTheory.TanVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBirationalImageEqTupleHeight
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem GlobalTheory.HSCore.isHeight_imageHeight : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), IsTotallyComplex F → T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → T.IsHeight (CompHt.imageHeight Nm W ev T.D) := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hF hT hB hP
  obtain ⟨h, hh⟩ := GlobalTheory.Adelic.HeightExists.exists_isHeight F T.toHermSys hT.alg
    (GlobalTheory.ImageDegree.degree_image_eq_topSelf hQ F T.toLinSys hT.alg.variety hT.alg.bpf hB).1
  have h1 := hP.isImageHeight hh
  rwa [_root_.GlobalTheory.ImageHeightFrame.isImageHeight_unique hQ F V Ω Nm W ev T.D _ h hF (CompHt.isImageHeight_imageHeight ⟨h, h1⟩) h1]
end

