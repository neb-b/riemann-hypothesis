module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0176
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

theorem homAt_comp' {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetSubstP_mk_X {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetCopy_mkX {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (j : Fin d) :
    jetCopy (S := S) d m i (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_psIn {S : Type} [CommRing S] {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n')
    (f : MvPowerSeries (Fin n × Fin d) S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  unfold psIn
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h
    simpa using hf
  · rfl

end GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf


open PeOne in
theorem peG_act_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val (peG t x d g.x g.e (p + m + 1) ![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (homAt x (jq w p m)).left z J = 1 := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w m hp z J hJ
  have hring : (jq w p m).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
      (![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j),
        fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) q.1 q.2) =
      ((jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2))).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
        (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k)
          q.1 q.2) := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun q => ?_)
    obtain ⟨a, j⟩ := q
    show _ = _
    simp only [AlgHom.comp_apply]
    refine Eq.trans (congrArg (jq w p m) (jetSubstP_mk_X _ _ _)) ?_
    refine Eq.trans ?_ (congrArg (fun u => jq w p m (jetCopy d (p + m + 1) (1 : Fin 2) u)) (jetSubstP_mk_X _ _ _)).symm
    fin_cases a
    · have h0 := _root_.GlobalTheory.CompanionTheory.Ar.Coc.actp_vanish E H hstar X0 t k p x d g w m hp j
      have hc := constantCoeff_psIn (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j) (g.B.A.const _ _)
      simp [hc, h0]
    · simp [jetCopy_mkX]
  have hcomp := congrArg (fun f => (homAt x f).left) hring
  simp only [homAt_comp', Over.comp_left] at hcomp
  refine (val_pull hJ _ _ _).trans ?_
  rw [hcomp]
  refine (val_pull hJ _ _ _).symm.trans ?_
  exact (val_corr hJ (g.axes _).1 _).trans (val_one _)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genPt_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (ξ : Sp K ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ := by
  unfold genPt
  show ξ ((spMap i) (closedPoint Ω)) = ξ (closedPoint K)
  congr 1
  first
  | exact Subsingleton.elim _ _
  | exact IsLocalRing.comap_closedPoint i
  | exact (IsLocalRing.PrimeSpectrum.comap_closedPoint i)

theorem finite_descResidueField_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω)
    (hi : i.Finite) (ξ : Sp K ⟶ X) (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (spMap i ≫ ξ))).hom.Finite := by
  have hA : ∀ p : Sp K, (ξ.stalkMap p).hom.Finite := by
    intro p
    obtain rfl : p = closedPoint K := Subsingleton.elim _ _
    apply RingHom.Finite.of_surjective
    have e : Scheme.stalkClosedPointTo ξ =
        ξ.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (CommRingCat.of K)).hom := by
      first
      | rfl
      | simp [Scheme.stalkClosedPointTo]
    intro y
    obtain ⟨a, ha⟩ := hξ ((stalkClosedPointIso (CommRingCat.of K)).hom y)
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1
    rw [← ha, e]
    rfl
  have hB : (Scheme.stalkClosedPointTo (spMap i)).hom.Finite := by
    change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i))).hom.Finite
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom i)
    refine RingHom.Finite.of_comp_finite
      (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) trivial).hom) ?_
    rw [← CommRingCat.hom_comp, Category.assoc, h, Iso.inv_hom_id_assoc]
    simpa using hi
  have hC : (Scheme.stalkClosedPointTo (spMap i ≫ ξ)).hom.Finite := by
    have e2 := Scheme.stalkClosedPointTo_comp (R := CommRingCat.of Ω) (spMap i) ξ
    have h3 := hB.comp (hA ((spMap i) (closedPoint Ω)))
    rw [← CommRingCat.hom_comp] at h3
    first
    | exact e2 ▸ h3
    | exact (congrArg (fun φ => (CommRingCat.Hom.hom φ).Finite) e2).mpr h3
    | (rw [e2]; exact h3)
  refine RingHom.Finite.of_comp_finite (f := (X.residue _).hom) ?_
  rw [← CommRingCat.hom_comp, Scheme.residue_descResidueField]
  exact hC

theorem levelCover : LevelCoverSt := by
  intro E _ _ _ H D l Xo c Y e he N hN
  obtain ⟨K, _, _, n0, x0, y0, htie, -, hgen⟩ := _root_.GlobalTheory.CompanionTheory.Ar.XR.exists_cpt_of_genericPoint E H D l Xo c Y e he
  obtain ⟨Ω, _, _, z, ev, hfd, hfull⟩ := _root_.GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite E H D l Xo c _ _ Y K y0 N hN
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : NumberField c.F :=
    { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hproj : IsProjOver (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F))) :=
    _root_.GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int _ Y.X Y.s Y.proj
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo (y0 ≫ Y.j)).hom := by
    obtain ⟨hg, -, -, -⟩ := htie
    obtain ⟨hb, -⟩ := hg
    exact hb.2
  have hi : (algebraMap K Ω).Finite := by
    first
    | exact RingHom.finite_algebraMap.mpr hfd
    | exact hfd
  have hfin := finite_descResidueField_spMap_comp (algebraMap K Ω) hi (y0 ≫ Y.j) hsurj
  obtain ⟨n, x, M, π, hMn, hπ, hMπ⟩ :=
    _root_.PositivityTheory.HtPt.Mf.xr_norm Y.X _ hproj Ω (spMap (algebraMap K Ω) ≫ (y0 ≫ Y.j)) hfin
  have hMg : IsCptGen M.ξ := by
    obtain ⟨hg, -, -, -⟩ := M.tie
    exact hg
  obtain ⟨t, hx, ev', h1, h2, h3⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over E H D l Xo c Y K Ω (algebraMap K Ω) y0 N z ev hN hfull M.X M.ξ hMg hMn π hMπ
  refine ⟨Ω, inferInstance, inferInstance, n, x, M, π, spMap (algebraMap K Ω) ≫ y0, t, hx, z, ev',
    hMn, hπ, ?_, ?_, h1, h2, h3⟩
  · show genPt (M.ξ ≫ π) = e
    rw [hMπ, genPt_spMap_comp, hgen]
  · rw [hMπ, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponent
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebraStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properness_descends_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsQProjOver p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_fg_isProper_of_isQProjOver <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TheoremOfCubeSectionValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_section_value : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {T : Over S} (x a : T ⟶ G) (m : ℕ), x ^ m = 1 → ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U), v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_lin_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_value_line_bundle_section : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts <;> assumption)
end

