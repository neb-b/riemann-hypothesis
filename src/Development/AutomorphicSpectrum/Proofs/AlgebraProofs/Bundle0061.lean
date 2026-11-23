module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0060
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0041
public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.Bundle0015
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @PositivityTheory.Xgf.exists_local_basis' | exact PositivityTheory.Xgf.exists_local_basis'
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitAffineNeighbourhoodStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_affine_neighbourhood : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → ∀ (x : X.left) (U : X.left.Opens), IsAffineOpen U → orbit G X x ⊆ U → ∃ (V : X.left.Opens) (W : S.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ V ≤ X.hom ⁻¹ᵁ W ∧ (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_stable_affine_nbhd | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_stable_affine_nbhd | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_stable_affine_nbhd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrdinaryCurveOfHodgeTate
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

theorem nonempty_padicInt_hom (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (hc : IsAdicComplete (Ideal.span {(p : R)}) R) : Nonempty (ℤ_[p] →+* R) := by
  haveI := hc
  have hd : ∀ n : ℕ, ringChar (R ⧸ (Ideal.span {(p : R)}) ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
  refine ⟨IsAdicComplete.liftRingHom (Ideal.span {(p : R)})
    (fun n => (ZMod.castHom (hd n) (R ⧸ (Ideal.span {(p : R)}) ^ n)).comp
      (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

variable {R : Type} [CommRing R]

theorem isTorsPts_comp {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N N' : Type}
    [AddCommGroup N] [AddCommGroup N'] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) (e : N' ≃+ N) : IsTorsPts G p (fun x => pt (e x)) := by
  refine ⟨h.inj.comp e.injective, ?_, ?_⟩
  · intro x y
    simpa using h.add (e x) (e y)
  · intro z
    rw [h.range z]
    exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩

theorem torsFun_comp {C : Type} [Field C] [Algebra R C] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] {p : ℕ} (T : TorsRep G p) {N N' : Type} [AddCommGroup N] [AddCommGroup N'] (pt : N → (sp (R₀ := R) R ⟶ G))
    (e : N' ≃+ N) :
    torsFun C T (fun x => pt (e x)) =
      (torsFun C T pt).map (LinearMap.funLeft R C (e : N' → N)) := by
  ext f
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun x => f (e.symm x), ⟨a, fun x φ h => ?_⟩, ?_⟩
    · exact ha (e.symm x) φ (by simpa using h)
    · ext x
      simp [LinearMap.funLeft_apply]
  · rintro ⟨g, ⟨a, ha⟩, rfl⟩
    exact ⟨a, fun x φ h => ha (e x) φ h⟩

theorem pt_zero {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N : Type}
    [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (h : IsTorsPts G p pt) : pt 0 = 1 := by
  have := h.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem exists_far {p : ℕ} {C : Type} [Field C] [Algebra R C] {v : Valuation C NNReal}
    (hv : v.Integers R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p)
    {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (hpt : IsTorsPts G p pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ t : N, ∃ g ∈ torsFun C T pt, v (g t - g 0) = 1 := by
  haveI : IsLocalRing R := isLocal_of_integers hv
  obtain ⟨t, rfl⟩ := (hpt.range z).1 hz
  have hex : ∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  choose φ hφ hφu using hex
  let k := IsLocalRing.ResidueField R
  have hne : (Algebra.ofId R k).comp (φ t) ≠ (Algebra.ofId R k).comp (φ 0) := by
    intro e
    apply hk k
    rw [← hφ t, ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hφ 0,
      pt_zero hpt]
    exact MonObj.comp_one _
  obtain ⟨a, ha⟩ : ∃ a, (Algebra.ofId R k) (φ t a) ≠ (Algebra.ofId R k) (φ 0 a) := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgHom.ext hcon)
  refine ⟨t, fun x => algebraMap R C (φ x a), ⟨a, fun x ψ h => ?_⟩, ?_⟩
  · rw [hφu x ψ h]
  · have hu : IsUnit (φ t a - φ 0 a) := by
      by_contra hn
      apply ha
      have hm : φ t a - φ 0 a ∈ IsLocalRing.maximalIdeal R := hn
      have := (Ideal.Quotient.eq_zero_iff_mem).2 hm
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [← map_sub]
    exact hv.one_of_isUnit hu

theorem exists_colen {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    (H : HodgeTateDatum p 1 v R ℤ_[p] AlgEquiv.refl cp) :
    ∃ cN, HasColen R v H.AA.carrier cN ∧ cN ^ 2 = v (p : C) ^ (p ^ 2) := by
  have hall := hgp p 1 C v R ℤ_[p] AlgEquiv.refl cp hs H
  dsimp only at hall
  obtain ⟨cA, cN, cO, -, hN, hO, -, hON⟩ := hall.2.2.2.2.2.2.2.2
  refine ⟨cN, hN, ?_⟩
  have hlen : HasLen v R (OmAA H.AA.carrier) (v (p : C)) := by
    refine ⟨1, fun _ => (p : R), ⟨?_⟩, by simp⟩
    exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
      ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p 1))
  have hc : cO = v (p : C) := hasLen_unique hs.integers hO hlen
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  rw [← hON, hc, hcard]

theorem reindex {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hlt : v (p : C) < 1)
    (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) (g : ℕ) (hg : g = 1)
    (H : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p g → (sp (R₀ := R) R ⟶ G))
    (hpt : IsTorsPts G p pt) (hH : H.AA.carrier = torsFun C T pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ pt' : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ G), IsTorsPts G p pt' ∧ torsFun C T pt' =
      tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
        (intFun R (ZMod p)) := by
  subst hg
  obtain ⟨cN, hN, hcN⟩ := exists_colen hgp hs H
  have hfar : ∃ t : Nb p 1, ∃ f ∈ H.AA.carrier, v (f t - f 0) = 1 := by
    rw [hH]
    exact exists_far hs.integers T hpt hz hk
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  have hkill : ∀ x : Nb p 1, p • x = 0 := fun x => by
    ext i
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.order_p_squared_extremal_colength p C v R hs.integers hlt (Nb p 1) hkill hcard H.AA cN hN hcN hfar
  refine ⟨fun x => pt (e x), isTorsPts_comp hpt e, ?_⟩
  rw [torsFun_comp, ← hH, he]

end GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem ordinaryCurve_of_hodgeTate : HodgeTateDatumStatement → OrdinaryCurveStatement := by
  intro hht p _ C _ _ _ v R _ _ hv hlt hc
  obtain ⟨f⟩ := OrdCurve.nonempty_padicInt_hom p R hc
  letI : Algebra ℤ_[p] R := f.toAlgebra
  obtain ⟨P, z, hg, hz, hk⟩ := GlobalTheory.T.polarised_abelian_variety_p_torsion p C v R hv hlt hc
  obtain ⟨⟨T⟩, cp, hs, H, pt, hpt, hH⟩ := hht p C v R hv hlt hc P
  obtain ⟨pt', h1, h2⟩ := OrdCurve.reindex _root_.GlobalTheory.CompanionTheory.Ar.GR.polarisedAF hlt hs T P.g hg H pt hpt (hH T) hz hk
  exact ⟨P.A, P.grp, P.L, P.isAb, P.isLB, P.ample, T, pt', h1, h2⟩

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingValuationSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_valuationSubring_of_padicEmbedding :
    ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]),
      ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧
        ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  intro F p κ
  have hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b =>
    IsUltrametricDist.norm_add_le_max a b
  have hone : ‖κ 1‖ = 1 := by simp
  let A : Subring ℂ :=
    { carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1}
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x * y, by simp, ?_⟩
        rw [map_mul, norm_mul]
        exact mul_le_one₀ hx (norm_nonneg _) hy
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x + y, by simp, ?_⟩
        rw [map_add (f := _)]
        exact (hna _ _).trans (max_le hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        exact ⟨-x, by simp, by simpa using hx⟩ }
  let I : Ideal A :=
    { carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1}
      add_mem' := by
        rintro a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩
        refine ⟨x + y, by simp [hxa, hyb], ?_⟩
        rw [map_add (f := _)]
        exact (hna _ _).trans_lt (max_lt hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro ⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩
        refine ⟨z * x, by simp [hzc, hxa], ?_⟩
        rw [map_mul, norm_mul]
        calc ‖κ z‖ * ‖κ x‖ ≤ 1 * ‖κ x‖ := by gcongr
          _ < 1 := by simpa using hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := by rw [htop]; trivial
    obtain ⟨x, hx1, hx⟩ := h1
    have hx1' : x = 1 := by
      apply Subtype.ext
      simpa using hx1
    rw [hx1', hone] at hx
    exact lt_irrefl _ hx
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits := by
    intro x hx
    have hxA : (x : ℂ) ∈ A := ⟨x, rfl, hx.le⟩
    exact hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩
  refine ⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩
  · have hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
        Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have := key ((p : ℕ) : F) (by simpa using hnorm)
    simpa using this
  · by_contra hlt
    have hlt' : 1 < ‖κ x‖ := not_le.mp hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hlt'
      linarith
    have hinv : ‖κ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt'
    have hnu := key x⁻¹ hinv
    rw [ValuationSubring.mem_nonunits_iff] at hnu
    have hle : W.valuation (x : ℂ) ≤ 1 := (W.valuation_le_one_iff _).2 hxW
    have hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1 := by
      rw [← map_mul]
      have : (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1 := by
        have h0 : (x : ℂ) ≠ 0 := by simpa using hx0
        simp [h0]
      rw [this, map_one]
    have : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu
    exact absurd hprod this.ne

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.QuotSide

section Act
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] (h : G ⟶ A) [IsMonHom h]

abbrev act : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction h A

lemma act_smul : (act h).smul = (fst G A ≫ h) * snd G A := by
  rw [Hom.mul_def]
  change h ▷ A ≫ μ[A] = _
  congr 1

end Act

theorem quotientByFiniteFlat_of_freeQuotient (hF : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme) :
    QuotientByFiniteFlatStatement := by
  intro R _ A _ L hA hL hamp B _ _ h hsub
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, hmon, hmono⟩ := GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub
  letI := act h
  have hgam : (γ[sp (R₀ := R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h
  have hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀ := R) B) (x : T ⟶ A),
      g • x = (g ≫ h) * x := by
    intro T g x
    rw [Hom.smul_def, hgam, comp_mul]
    simp
  have hample : GlobalTheory.IsAmpleLB L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀ := R) B).hom := by
    have e : (sp (R₀ := R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl
    have := hsub.proj
    have := hsub.fin
    have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
    have hfp : (algebraMap R B).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)
    rw [e]
    refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  have hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀ := R) B) A := by
    intro T g x hx
    rw [hsmul] at hx
    have h1 : g ≫ h = 1 := mul_eq_right.mp hx
    rw [← cancel_mono h, h1, MonObj.one_comp]
  have horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x ⊆ U := by
    intro x
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    have hs : IsFinite (snd (sp (R₀ := R) B) A).left := by
      rw [Over.snd_left]; infer_instance
    have hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x).Finite :=
      (Scheme.Hom.finite_preimage_singleton _ x).image _
    obtain ⟨n, -, s, h₁, -, h₂⟩ := hample.exists_affine_finite_subset hfin
      (U := ⊤) (fun _ _ => trivial)
    exact ⟨_, h₂, h₁⟩
  obtain ⟨Y, q, -, hT⟩ := hF _ (sp (R₀ := R) B) A hG hfree horb
  obtain ⟨hq1, hq2, hq3⟩ := hT.isFiniteLocallyFree hG
  have hq4 := hT.surjective
  have hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q := hgam ▸ hT.1
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨inst, hcomm, hhom, hker⟩ := GlobalTheory.AbelianQuotient.exists_grpObj h q hq
  have hw : q.left ≫ Y.hom = A.hom := Over.w q
  have hsnd : IsFinite (snd (sp (R₀ := R) B) A).left := by
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    rw [Over.snd_left]; infer_instance
  have hab : IsAbelianScheme Y := by
    have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated Y.hom := _root_.GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective q _ _ hq hsnd inferInstance hq1 hq4
    have : Flat (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyReduced (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyConnected (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom
    have := UniversallyClosed.of_comp_surjective q.left Y.hom
    have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom
    have : LocallyOfFinitePresentation Y.hom :=
      _root_.GlobalTheory.CompanionTheory.LfpDescent.descends q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)
    exact ⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩,
      GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩
  have := hab.proper
  obtain ⟨N, hN₁, hN₂⟩ := _root_.GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf q.left hq1 hq2 hq3
  obtain ⟨L', hL', hN⟩ := _root_.GlobalTheory.CompanionTheory.NormLB.exists_normLB q.left hq1 N hN₁ hN₂ L hL (by
    intro y
    obtain ⟨W, -, h₁, -, t⟩ := hample.exists_affine_finite_subset_trivial hL
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)
    exact ⟨W, fun x hx => h₁ hx, t⟩)
  refine ⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩
  · have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : CompactSpace Y.left := q.left.surjective.compactSpace q.left.continuous
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2
      (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)
    obtain ⟨n, hn, s, h₁, h₂, -⟩ := hample.exists_affine_finite_subset
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U)
      (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)
    obtain ⟨σ, hσ⟩ := hN n s
    refine ⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩
    obtain ⟨x, rfl⟩ := q.left.surjective y'
    exact h₂ ((hσ _).1 hy' x rfl)
  · intro S _ _ z
    have hhq : h ≫ q = 1 := hker.w.trans Hom.one_def.symm
    constructor
    · intro hz
      let y : sp (R₀ := R) S ⟶ sp (R₀ := R) B :=
        hker.lift z (toUnit _) (by rw [hz, Hom.one_def])
      have hy : y ≫ h = z := hker.lift_fst _ _ _
      obtain ⟨ψ, hψ⟩ := Spec.map_surjective y.left
      have hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ]
        exact Over.w y
      let φ : B →ₐ[R] S := { ψ.hom with
        commutes' := fun r => congr($hc r) }
      have hφ : spMap φ = y := Over.OverMorphism.ext hψ
      exact ⟨φ, by rw [hφ, hy]⟩
    · rintro ⟨φ, rfl⟩
      rw [Category.assoc, hhq, comp_one]

end GlobalTheory.CompanionTheory.Ar.GR.QuotSide
end
end

