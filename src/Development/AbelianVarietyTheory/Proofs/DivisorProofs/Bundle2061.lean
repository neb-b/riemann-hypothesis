module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_inv_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) :
    lam (cls L hL) x⁻¹ z = - lam (cls L hL) x z := by
  have h := lam_mul_left hL hΘ x⁻¹ x z
  rw [inv_mul_cancel, lam_one_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem lam_inv_inv {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) :
    lam (cls L hL) x⁻¹ y⁻¹ = lam (cls L hL) x y := by
  rw [lam_inv_left hL hΘ, lam_comm, lam_inv_left hL hΘ, lam_comm, neg_neg]

theorem lam_pull_inv (c : Pic G.left) (x y : T ⟶ G) :
    lam (pull (ι[G]).left c) x y = lam c x⁻¹ y⁻¹ := by
  simp only [lam, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, mul_inv, inv_one]

end GlobalTheory.PolDeg.NegPrim

namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

theorem lam_negPull_sub_isTrivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  intro A _ _ _ B _ _ M cub _
  have hΘ : ∃ t : LB.Gen (Theta B M.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  have hN : (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).IsLB := LB.isLB_linComb M.isLB _ _
  have hΛ : (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])).IsLB := LB.isLB_linComb hN _ _
  refine (cls_eq_zero_iff hΛ).1 ?_
  have hc : cls _ hN = pull (ι[B]).left (cls M.L M.isLB) - cls M.L M.isLB := by
    rw [cls_linComb M.isLB, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, sub_eq_add_neg]
  refine (cls_cube_two hN (fst B B) (snd B B) hΛ).trans ?_
  have e : ∀ (c c' : Pic B.left) (x y : B ⊗ B ⟶ B), lam (c - c') x y = lam c x y - lam c' x y := fun c c' x y => by
    simp only [lam, map_sub]; abel
  rw [hc, e, lam_pull_inv, lam_inv_inv M.isLB hΘ, sub_self]

end GlobalTheory.PolDeg.NegPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGenerators
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GenGlue

lemma isDominant_of_spec {K : Type} [Field K] {W : Scheme.{0}} (v : Sp K ⟶ W)
    (h : ∀ (q : Sp K) (z : W), v q ⤳ z) : IsDominant v :=
  ⟨fun z => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (IsLocalRing.closedPoint K)))
    (specializes_iff_mem_closure.1 (h _ z))⟩

theorem exists_glue : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) →
    ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P),
    (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) →
    ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  intro Y P _ _ U hU f w hw
  have hgp : ∀ q, gp Y q = genericPoint Y := fun q => by
    obtain rfl : q = IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : ∀ (V : Y.Opens) (y : Y), y ∈ V → genericPoint Y ∈ V := fun V y hy =>
    ((genericPoint_spec Y).mem_open_set_iff V.2).2 ⟨y, trivial, hy⟩
  have hlift : ∀ V : Y.Opens, genericPoint Y ∈ V →
      ∃ l : Sp Y.functionField ⟶ V.toScheme, l ≫ V.ι = gp Y := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (gp Y) (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨q, rfl⟩; rw [hgp]; exact hV), IsOpenImmersion.lift_fac _ _ _⟩
  have hdom : ∀ (V : Y.Opens) (l : Sp Y.functionField ⟶ V.toScheme), l ≫ V.ι = gp Y → IsDominant l := by
    intro V l hl
    refine isDominant_of_spec l fun q z => ?_
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e1 : V.ι (l q) = gp Y q := by rw [← hl]; rfl
    rw [e1, hgp]
    exact (genericPoint_spec Y).specializes trivial
  let g : Y → Y.PartialMap P := fun y => ⟨U y, (U y).2.dense ⟨y, hU y⟩, f y⟩
  have heq : ∀ y y', (g y).toRationalMap = (g y').toRationalMap := by
    intro y y'
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    let V := U y ⊓ U y'
    have hV : genericPoint Y ∈ V := ⟨hgen _ y (hU y), hgen _ y' (hU y')⟩
    obtain ⟨l, hl⟩ := hlift V hV
    haveI := hdom V l hl
    refine ⟨V, V.2.dense ⟨_, hV⟩, inf_le_left, inf_le_right, ?_⟩
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
    refine ext_of_isDominant l ?_
    rw [← Category.assoc, ← Category.assoc,
      hw y _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl]),
      hw y' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl])]
  let y0 := genericPoint Y
  let F := (g y0).toRationalMap
  have htop : F.domain = ⊤ :=
    top_le_iff.1 fun z _ => Scheme.RationalMap.mem_domain.2 ⟨g z, hU z, heq z y0⟩
  have htop' : F.toPartialMap.domain = ⊤ := htop
  let k : Y ⟶ F.toPartialMap.domain.toScheme := IsOpenImmersion.lift F.toPartialMap.domain.ι (𝟙 Y)
    (by rw [Scheme.Opens.range_ι, htop']; simp)
  have hk : k ≫ F.toPartialMap.domain.ι = 𝟙 Y := IsOpenImmersion.lift_fac _ _ _
  have hgpm : gp Y ≫ k ≫ F.toPartialMap.hom = w := by
    obtain ⟨l, hl⟩ := hlift (U y0) (hU y0)
    have h2 : (g y0).domain.ι ≫ k = Y.homOfLE (g y0).le_domain_toRationalMap := by
      apply (cancel_mono F.toPartialMap.domain.ι).1
      rw [Category.assoc, hk, Category.comp_id]
      exact (Scheme.homOfLE_ι _ _).symm
    rw [← hl]
    rw [Category.assoc, reassoc_of% h2]
    exact (congrArg (l ≫ ·) (g y0).toPartialMap_toRationalMap_restrict).trans (hw y0 l hl)
  refine ⟨k ≫ F.toPartialMap.hom, fun y => ?_, hgpm⟩
  obtain ⟨l, hl⟩ := hlift (U y) (hgen _ y (hU y))
  haveI := hdom _ l hl
  refine ext_of_isDominant l ?_
  rw [reassoc_of% hl, hgpm, hw y l hl]

end GlobalTheory.Desc.GenGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetween
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.GlobalPoly

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ v.asIdeal) : 0 < vLa v (p : K) := by
  have hne : (p : K) ≠ 0 := by exact_mod_cast hp0
  have hlt : v.valuation K (p : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hp
  have h0 : v.valuation K (p : K) ≠ 0 := by simpa using hne
  have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
  simp only [WithZero.log_one] at this
  simp only [vLa]; omega

theorem vV_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
  simp [vV, this]

theorem vV_prime_le (T : CDVR) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hv : 0 < vV T.V (p : T.Fr)) :
    vV T.V (q : T.Fr) ≤ vV T.V (p : T.Fr) := by
  by_cases hpq : q = p
  · subst hpq; exact le_rfl
  have hcop : IsCoprime ((q : ℤ)) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hpq)
  have hcopV : IsCoprime ((q : T.V)) (p : T.V) := by
    simpa using hcop.map (Int.castRingHom T.V)
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (p : T.V) := by
      by_contra h'; exact h ((IsLocalRing.mem_maximalIdeal _).2 h')
    have := vV_of_isUnit T hu
    rw [map_natCast] at this; omega
  have hqu : IsUnit (q : T.V) := by
    by_contra h'
    have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 h'
    obtain ⟨u, w, huw⟩ := hcopV
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [← huw]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := vV_of_isUnit T hqu
  rw [map_natCast] at this
  rw [this]; exact hv.le

end GlobalTheory.RefSum.GlobalPoly

theorem GlobalTheory.RefSum.GlobalPoly.exists_polyBetween : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn A B hNu
  obtain ⟨N, hN⟩ := exists_nat_gt (B + ∑ q ∈ D.host.condN.primeFactors,
    1 * D.host.vdH q * ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2)
  obtain ⟨P₁, hP₁, hglob⟩ := GlobalTheory.T.exists_global_harmonic_congr_column_polynomial D.host.E H Dw l Xo c p la a ha n hn N
  refine ⟨P₁, hP₁, fun T io e ho y hy Ch k => ?_⟩
  obtain ⟨Bc, R, hcols, hR, heq⟩ := hglob T io e ho
  have hchoice := GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth D.host.E H Dw l Xo c p la T io e ho y Ch (gap Dw a) n Bc hcols k
  have hv : 0 < vV T.V (p : T.Fr) := by
    rw [← map_natCast io p, ho.2]
    exact mul_pos (by exact_mod_cast ho.1) (GlobalTheory.RefSum.GlobalPoly.vLa_pos_of_mem la.1 hp.out.ne_zero la.2)
  have hve : vV T.V (p : T.Fr) = ((vV T.V (p : T.Fr)).toNat : ℤ) := (Int.toNat_of_nonneg hv.le).symm
  have he : 0 < (vV T.V (p : T.Fr)).toNat := by omega
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D H Dw l Xo c (fun _ => rfl) T io y Ch _ he a n
    (Formalism.L2.Pj.DF Dw a) le_rfl
  have hNu' := hNu T io e ho y
  have hpert := GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation D.host.E H Dw l Xo c p T io y Ch _ he hve a n N k _ B (polyT Bc (gap Dw a)) R hch hR
    (hchoice.trans_le (hNu'.2 hy)) (by
      refine lt_of_le_of_lt (add_le_add le_rfl (Finset.sum_le_sum fun q hq => ?_)) hN
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hle := GlobalTheory.RefSum.GlobalPoly.vV_prime_le T hp.out hqp hv
      have hr : (vV T.V (q : T.Fr) : ℝ) / ((vV T.V (p : T.Fr)).toNat : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast he)]
        rw [hve] at hle
        exact_mod_cast hle
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr (D.host.vdH_nonneg q)) (Nat.cast_nonneg _)) zero_le_two)
  rw [heq, hpert, hchoice]
  exact ⟨hNu'.1, hNu'.2 hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

theorem GlobalTheory.VolBr.Pair.exists_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  intro k _ X _ p P a b
  obtain ⟨hL, hA, -⟩ := Pair.rep_base k X p P
  have cast (x y x' y' : ℤ) (M : HermLB p) (h : P.Rep x y M) (hx : x = x') (hy : y = y') :
      P.Rep x' y' M := by subst hx; subst hy; exact h
  have hLa := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ a.toNat hL)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-a).toNat hL))
  have hAb := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  refine ⟨_, cast _ _ _ _ _ (Pair.rep_tens k X p P _ _ _ _ _ _ hLa hAb) ?_ ?_⟩
  · have h1 := Int.toNat_sub_toNat_neg a
    simp only [mul_one, mul_zero, neg_zero, add_zero]
    omega
  · have h1 := Int.toNat_sub_toNat_neg b
    simp only [mul_one, mul_zero, neg_zero, zero_add]
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_ringHom_fnOf_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] {U : Y.Opens}
    (hU : genericPoint Y ∈ U) {V : P.Opens} (hVη : genericPoint P ∈ V)
    (φ : P.functionField →+* Y.functionField) (h : ∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) :
    ∃ ψ : Γ(P, V) →+* Γ(Y, U), ∀ s, fnOf U hU (ψ s) = φ (fnOf V hVη s) := by
  choose t ht using fun s => exists_fnOf_eq hU (h s)
  refine ⟨⟨⟨⟨t, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, ht⟩ <;> apply fnOf_injective U hU
  · rw [ht, map_one, map_one, map_one]
  · rw [map_mul, ht, ht, ht, map_mul, map_mul]
  · exact (ht 0).trans (by rw [map_zero, map_zero, map_zero])
  · exact (ht (a + b)).trans (((congrArg φ (map_add _ a b)).trans (map_add φ _ _)).trans
      ((congrArg₂ (· + ·) (ht a) (ht b)).symm.trans (map_add (fnOf U hU) (t a) (t b)).symm))


set_option backward.isDefEq.respectTransparency false in
theorem exists_hom_of_regAt_fnOf : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  intro Y P _ _ U hU V hV hVη φ h
  obtain ⟨ψ, hψ⟩ := exists_ringHom_fnOf_eq hU hVη φ h
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun y => ?_, fun l hl => ?_⟩
  · rw [← Category.assoc, Scheme.Hom.comp_apply]
    change _ ∈ (V : Set P)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  · obtain rfl : l = U.fromSpecStalkOfMem (genericPoint Y) hU := by
      rw [← cancel_mono U.ι, hl]
      exact (Scheme.Opens.fromSpecStalkOfMem_ι U _ hU).symm
    have e : CommRingCat.ofHom ψ ≫ Y.presheaf.germ U (genericPoint Y) hU =
        P.presheaf.germ V (genericPoint P) hVη ≫ CommRingCat.ofHom φ := by
      ext s
      exact hψ s
    have e₁ := Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc U (genericPoint Y) hU
      (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    refine e₁.trans ?_
    rw [← Spec.map_comp_assoc]
    refine (congrArg (fun z => Spec.map z ≫ hV.fromSpec) e).trans ?_
    rw [gp, ← hV.fromSpecStalk_eq_fromSpecStalk hVη, IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc]

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousCorrectionNextThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem veryAmpleBy_comp_quotient {X : Scheme.{0}} {R : Type} [CommRing R] (J : Ideal R)
    (f : X ⟶ Spec (CommRingCat.of (R ⧸ J))) (H : LB X) {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (h : VeryAmpleBy f H s) :
    VeryAmpleBy (f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) H s := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨ha, r, hr, hsurj⟩ := h2 i
  refine ⟨ha, r, hr, fun y => ?_⟩
  obtain ⟨P, rfl⟩ := hsurj y
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P
  refine ⟨P', ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, cst_comp_spec]

theorem exists_homogeneous_correction_succ : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, AddMonoidAlgebra.coeff G d ∈ I ^ (e + 1)) ∧ F - G ∈ vanIdeal ((Y (e + 1)).hom ≫ thick R I (e + 1)) (s (e + 1)) := by
  intro R _ _ I Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have hVAR : ∀ e, VeryAmpleBy ((Y e).hom ≫ thick R I e) (H e) (s e) := fun e =>
    veryAmpleBy_comp_quotient _ _ _ _ (hVA e)
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hpb := (_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).1
  exact _root_.GlobalTheory.homogeneous_correction_next_level R I n (fun e => vanIdeal ((Y e).hom ≫ thick R I e) (s e))
    (fun e _ _ _ h => mem_vanIdeal_of_sat _ _ (hVA e).1 h)
    (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
      rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
    (fun e t F hF hK i => _root_.GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left
      ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom (hpb e) (H (e + 1)) (H e) (v e) n (s (e + 1)) (s e)
      (hH _).1 (hH _).1 (hH e).2 (hs e) (hVAR (e + 1)) t F hF (by rw [c₁]; exact hK) i)

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstants
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem LiftSys.cobound_I : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc S z hz h0
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h0
  obtain ⟨r₀, hr₀⟩ := hc (fun U ↦ S.p U (g U)) (by
    funext U V a
    have e := congrFun (congrFun (congrFun hg U) V) a
    rw [amitsur_d0_apply] at e
    rw [amitsur_d0_apply, ← S.nat a, ← map_sub, e]
    exact (S.ker V _).2 (hz U V a))
  obtain ⟨r, rfl⟩ := hπ r₀
  refine ⟨fun U ↦ g U - algebraMap R (S.F.obj U) r, fun U ↦ (S.ker U _).1 ?_, ?_⟩
  · rw [map_sub, hr₀ U, (S.semi U).map_algebraMap, sub_self]
  · rw [← hg]
    funext U V a
    simp only [amitsur_d0_apply, map_sub, AlgHom.commutes]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismsIntoAffineOpenMilnorSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare : ∀ (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ (V : U.left.Opens), IsAffineOpen V → ∀ (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U), k₁ ≫ u₁ = k₂ ≫ u₂ → (∀ x, u₁.left x ∈ V) → (∀ x, u₂.left x ∈ V) → ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  first | exact @GlobalTheory.DualOpen.glue_into_affineOpen | exact GlobalTheory.DualOpen.glue_into_affineOpen | (intros; apply GlobalTheory.DualOpen.glue_into_affineOpen <;> assumption)
end

