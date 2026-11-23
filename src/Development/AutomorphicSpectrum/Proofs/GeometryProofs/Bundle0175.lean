module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionJet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Actp


open MvPolynomial in
theorem aug_jetMap {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R)
    (hφ : ∀ i, φ i ∈ orig R κ') :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetMap φ hφ) = jetAug := by
  refine GermD.jet_hom_ext fun i => ?_
  have hk : ∀ P ∈ orig R κ', (aeval (fun _ : κ' => (0 : R))) P = 0 := by
    intro P hP
    have : orig R κ' ≤ RingHom.ker ((aeval (fun _ : κ' => (0 : R)) : MvPolynomial κ' R →ₐ[R] R) : MvPolynomial κ' R →+* R) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      simp [RingHom.mem_ker]
    exact this hP
  have e1 : (jetAug : Jet R κ' m →ₐ[R] R) ((jetMap φ hφ) (Ideal.Quotient.mk _ (X i))) = aeval (fun _ : κ' => (0 : R)) (φ i) := by
    rw [GermD.jetMap_mk, aeval_X]; rfl
  have e2 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (X i)) = 0 := by
    show aeval (fun _ : κ => (0 : R)) (X i) = 0
    simp
  rw [AlgHom.comp_apply, e1, e2, hk _ (hφ i)]

theorem aug_subst {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' R) (z : Jet R κ m) :
    (jetAug : Jet R κ' m →ₐ[R] R) (jetSubstP m φ z) = (jetAug : Jet R κ m →ₐ[R] R) z :=
  DFunLike.congr_fun (aug_jetMap (m := m) (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i)))
    (fun _ => sub_const_mem_orig _)) z

theorem aug_X {R : Type} [CommRing R] {κ : Type} (m : ℕ) (q : κ) :
    (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0
  simp

theorem homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Val

open MvPolynomial

variable {k : Type} [Field k] {d : ℕ}

theorem subst_mk (w : Fin d → k) (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (aeval (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k)) P) := by
  have h : (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k) -
      C (constantCoeff (C (w q.2) * X () : MvPolynomial Unit k))) = fun q => C (w q.2) * X () := by
    funext q
    simp
  rw [CIndFrExp2.jetSubstP_mk, h]

def vW (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) : Fin 1 × Fin d → Jet B Unit p :=
  fun q => algebraMap k _ (w q.2) * dQ B p

theorem aeval_vW_orig (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ)
    (P : MvPolynomial (Fin 1 × Fin d) k) (hP : P ∈ orig k (Fin 1 × Fin d) ^ (p + 1)) :
    aeval (vW w B p) P = 0 := by
  have h1 : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
      MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) P ∈
      Ideal.map ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (orig k (Fin 1 × Fin d) ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h1
  have h2 : Ideal.span (Set.range fun i =>
      ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X i)) ≤ Ideal.span {dQ B p} := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    have : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X q) = vW w B p q := by simp
    beta_reduce
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h3 := Ideal.pow_right_mono h2 (p + 1) h1
  rw [dQ_span_pow] at h3
  exact (Submodule.mem_bot _).1 h3

theorem inL_subst (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    inL (k := k) B p (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P)) =
      aeval (vW w B p) P := by
  rw [subst_mk]
  have e : ∀ Q : MvPolynomial Unit k, inL (k := k) B p (Ideal.Quotient.mk _ Q) = aeval (fun _ => dQ B p) Q := fun _ => rfl
  rw [e, ← AlgHom.comp_apply, comp_aeval]
  have h : (fun q : Fin 1 × Fin d => (aeval (R := k) (fun _ : Unit => dQ B p)) (C (w q.2) * X () : MvPolynomial Unit k)) =
      vW w B p := by
    funext q
    simp [vW]
  exact congrArg (fun u => aeval u P) h

theorem jq_first (w : Fin d → k) (p m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) k) :
    jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      inL (k := k) (Jet k (Fin 1 × Fin d) m) p
        (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ (psTrunc p f))) := by
  have e1 : jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      aeval (vW w (Jet k (Fin 1 × Fin d) m) p) (psTrunc (p + m + 1) f) := by
    show aeval _ (rename _ (psTrunc (p + m + 1) f)) = _
    rw [aeval_rename]
    refine congrArg (fun u => aeval u (psTrunc (p + m + 1) f)) ?_
    funext q
    simp [vW]
  rw [e1, inL_subst, ← sub_eq_zero, ← map_sub]
  exact aeval_vW_orig w _ p _ (CIndFrExp2.psTrunc_sub_mem f (by omega))

end Val

end GlobalTheory.CompanionTheory.Ar.Coc.Actp

namespace GlobalTheory.CompanionTheory.Ar.Coc


open MvPolynomial in
theorem actp_at_point {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hst : ∀ a : 𝓞 E, star a = H.bar a) {X0 : Scheme.{0}} (t : SAB H X0) {k : Type} [Field k] (p : ℕ)
    (x : Sp k ⟶ X0) {d : ℕ} (g : GermAt t x d)
    (σ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p)
    (hσ : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ z) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z)
    (hy : (homAt x σ ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1) (j : Fin d) :
    σ (Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k (Fin 1 × Fin d) p,
      ψ = jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2) := ⟨_, rfl⟩
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p,
      χ₀ = (Algebra.ofId k (Jet k Unit p)).comp (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) := ⟨_, rfl⟩
  have e : g.x p ≫ t.act.act (p : 𝓞 E) = homAt x ψ ≫ g.x p := by
    rw [hψ]; exact g.chart.act p (p : 𝓞 E)
  have h1 : homAt x (σ.comp ψ) ≫ g.x p = 1 := by
    rw [Actp.homAt_comp, Category.assoc, ← e, ← Category.assoc,
      PullbackSections.act_natCast, MonObj.comp_pow, Category.comp_id]
    exact hy
  have h0 : homAt x χ₀ ≫ g.x p = 1 := by
    rw [hχ₀, Actp.homAt_comp, Category.assoc, g.chart.zero p, MonObj.comp_one]
  have a1 : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ (ψ z)) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z := by
    intro z
    rw [hσ, hψ, Actp.aug_subst]
  obtain ⟨χ, -, huniq⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal E H hst X0 t k x d g).2 Unit p 1 (MonObj.comp_one _)
  have c1 := huniq (σ.comp ψ) ⟨fun q => by rw [AlgHom.comp_apply, a1, Actp.aug_X], h1.symm⟩
  have c0 := huniq χ₀ ⟨fun q => by
    simp only [hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero], h0.symm⟩
  have c : σ.comp ψ = χ₀ := c1.trans c0.symm
  have hc : MvPowerSeries.constantCoeff (g.B.A.act (p : 𝓞 E) j) = 0 := g.B.A.const _ _
  have cc : constantCoeff (psTrunc p (g.B.A.act (p : 𝓞 E) j)) = 0 := by
    have h := GermFun.coeff_psTrunc p (g.B.A.act (p : 𝓞 E) j) 0 (by simp)
    rw [MvPolynomial.constantCoeff_eq, h]
    simpa using hc
  have e' : ψ (Ideal.Quotient.mk _ (X ((0 : Fin 1), j))) = Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j)) := by
    rw [hψ, CIndFrExp2.jetSubstP_mk, aeval_X, cc, map_zero, sub_zero]
  have e2 := DFunLike.congr_fun c (Ideal.Quotient.mk _ (X ((0 : Fin 1), j)))
  rw [AlgHom.comp_apply, e', hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero] at e2
  exact e2

theorem actp_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ j, jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  intro E _ _ _ H _ hst X0 t k _ p _ _ x d g w m hy j
  rw [Actp.jq_first, actp_at_point H hst t p x g _ (fun z => Actp.aug_subst p _ z) hy j, map_zero]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.LabConst

theorem valAt_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ)) (o : O) (r : R)
    (h : ValAt ξ z (algebraMap O Ω o) r) : r = ρ o := by
  obtain ⟨hsp, t, ht, rfl⟩ := h
  have hg' := ConstReg.genMap_germ_const ξ s hs ⟨centre z, hsp⟩ o
  have ht' := hg.inj ⟨centre z, hsp⟩ (ht.trans hg'.symm)
  rw [ht']
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem const_of_root {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (p : Polynomial ℤ) (hp : p.Monic)
    (hr : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, Polynomial.aeval (f b) p = 0)
    {b b' : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) 1) (hb' : b' ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    f b = f b' := by
  have hne : p.map (Int.castRingHom ℂ) ≠ 0 := (hp.map _).ne_zero
  have hfin : ((p.map (Int.castRingHom ℂ)).rootSet ℂ).Finite := Polynomial.rootSet_finite _ _
  haveI : Finite ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := hfin
  haveI : DiscreteTopology ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := inferInstance
  refine IsPreconnected.constant_of_mapsTo (convex_ball _ _).isPreconnected
    (T := (p.map (Int.castRingHom ℂ)).rootSet ℂ) ⟨inferInstance⟩ hf.continuousOn (fun x hx => ?_) hb hb'
  rw [Polynomial.mem_rootSet]
  refine ⟨hne, ?_⟩
  have h := hr x hx
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq] at h
  rw [Polynomial.coe_aeval_eq_eval]
  exact h

theorem labVal_const_of_isHolPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 R _ jj n ψ hψ
  have hB : ∀ b : Fin n → ℂ, ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ),
      𝔐.LabVal (spMap (ψ b) ≫ jj) id σ ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
    intro b
    obtain ⟨σ, h1, -, -, -, -, h6⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal E H D l Xo c Y S Ω K J y 𝔐 ℂ (spMap (ψ b) ≫ jj)
    obtain ⟨h7, h8, -⟩ := h6 (RingHom.id ℂ)
    exact ⟨σ, h1, by simpa using h7, by simpa using h8⟩
  choose σ hσ hc1 hc2 using hB
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = jj ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (jj ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have key : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ∃ r : R, ∀ b, σ b s a = ψ b r := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    refine ⟨ρ (IsIntegralClosure.mk' (𝓞 c.F) _ hint), fun b => ?_⟩
    refine valAt_const 𝔐.ξ 𝔐.tie.gen (𝔐.f ≫ Y.s) 𝔐.cst_over (spMap (ψ b) ≫ jj) ((ψ b).comp ρ) ?_ _ _ ?_
    · rw [Category.assoc, ← hρ]; simp [spMap]
    · have h := hσ b s a
      have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb (id s) a := by
        show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
        rw [IsIntegralClosure.algebraMap_mk']
      rw [he]; exact h
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hconst : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, σ b = σ 0 := by
    intro b hb
    funext s
    refine RingHom.ext fun a => ?_
    obtain ⟨r, hr⟩ := key s a
    obtain ⟨p, hpm, hpe⟩ := NumberField.RingOfIntegers.isIntegral a
    refine const_of_root (fun b => σ b s a) ?_ p hpm ?_ hb h0
    · have : (fun b => σ b s a) = fun b => ψ b r := funext hr
      rw [this]; exact hψ.2 r
    · intro x _
      have h1 : Polynomial.aeval a p = 0 := hpe
      have h2 : Polynomial.aeval (σ x s a) p = (σ x s).toIntAlgHom (Polynomial.aeval a p) :=
        Polynomial.aeval_algHom_apply (σ x s).toIntAlgHom a p
      rw [h2, h1, map_zero]
  refine ⟨σ 0, fun b hb => ?_, hc1 0, hc2 0⟩
  rw [← hconst b hb]
  exact hσ b

end GlobalTheory.CompanionTheory.Ar.Flat.LabConst
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.KerBd

variable {k : Type} [Field k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Wd (B : Germ.FB k d O) (a : O) : Submodule k (Fin d → k) where
  carrier := {u | (rho B a).mulVec u = 0 ∧ ∀ z : Fin d → k, (rho B (star a)).mulVec z = 0 →
      z ⬝ᵥ (bil (B.ad a) 1 1).transpose.mulVec u = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by simp [Matrix.mulVec_add, hu1, hv1], fun z hz => ?_⟩
    simp [Matrix.mulVec_add, dotProduct_add, hu2 z hz, hv2 z hz]
  zero_mem' := ⟨by simp, fun z _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    refine ⟨by simp [Matrix.mulVec_smul, hu1], fun z hz => ?_⟩
    simp [Matrix.mulVec_smul, dotProduct_smul, hu2 z hz]

theorem Wd_le (B : Germ.FB k d O) (a : O) : Wd B a ≤ LinearMap.ker (Matrix.toLin' (rho B a)) :=
  fun u hu => by simpa [Matrix.toLin'_apply] using hu.1

theorem finrank_ker_transpose (M : Matrix (Fin d) (Fin d) k) :
    Module.finrank k (LinearMap.ker (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M.transpose)
  have h3 : Module.finrank k (LinearMap.range (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.range (Matrix.toLin' M)) := by
    have := Matrix.rank_transpose M
    rw [Matrix.rank, Matrix.rank] at this
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
    convert this using 2
  omega

theorem finrank_ker_rhoH_le (B : Germ.FB k d O) (a : O) :
    Module.finrank k (LinearMap.ker (rhoH B a)) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)))) + Module.finrank k (Wd B a) := by
  set K := LinearMap.ker (rhoH B a)
  let f : K →ₗ[k] (Fin d → k) := (LinearMap.fst k (Fin d → k) (Fin d → k)).comp K.subtype
  have hrange : LinearMap.range f ≤ Wd B a := by
    rintro _ ⟨y, rfl⟩
    have hy : rhoH B a y = 0 := y.2
    rw [rhoH_apply, Prod.mk_eq_zero] at hy
    refine ⟨hy.1, fun z hz => ?_⟩
    have h2 : (bil (B.ad a) 1 1).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).1 =
        (rho B (star a)).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).2 := (sub_eq_zero.1 hy.2).symm
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.fst_apply]
    rw [h2, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz, zero_dotProduct]
  let g : LinearMap.ker f →ₗ[k] (Fin d → k) :=
    (LinearMap.snd k (Fin d → k) (Fin d → k)).comp (K.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have h2 : ((y : K) : (Fin d → k) × (Fin d → k)).2 = 0 := hy
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  have hgr : LinearMap.range g ≤ LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose) := by
    rintro _ ⟨y, rfl⟩
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have hy : rhoH B a (y : K) = 0 := (y : K).2
    rw [rhoH_apply, Prod.mk_eq_zero, h1] at hy
    simpa [g, Matrix.toLin'_apply] using hy.2
  have e1 := LinearMap.finrank_range_add_finrank_ker f
  have e2 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (Wd B a) := Submodule.finrank_mono hrange
  have e3 : Module.finrank k (LinearMap.ker f) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose)) := by
    rw [← LinearMap.finrank_range_of_inj hg]; exact Submodule.finrank_mono hgr
  rw [finrank_ker_transpose] at e3
  omega

end GlobalTheory.CompanionTheory.Ar.Flat.KerBd

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.KerBd in
theorem lemF_ker_order_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  intro E _ _ _ H _ hbar k _ _ p _ _ t hprop hK d g a A _ _ _ i hpb
  obtain ⟨A', _, _, _, _, hrk, D, T, hD, hT, hder, hprim, horth⟩ :=
    GlobalTheory.T.proper_group_germ_finite_subscheme E H hbar k p t hprop hK d g a A i hpb
  let W0 : Submodule k (LinearMap.ker (Matrix.toLin' (rho g.B a))) :=
    (Wd g.B a).comap (LinearMap.ker (Matrix.toLin' (rho g.B a))).subtype
  have hW0 : Module.finrank k W0 = Module.finrank k (Wd g.B a) :=
    (Submodule.comapSubtypeEquivOfLe (Wd_le g.B a)).finrank_eq
  have hc := GlobalTheory.T.primitive_derivation_pairing k p A' (LinearMap.range T) (W0.map D)
    (by rintro _ ⟨z, rfl⟩; exact hprim z)
    (by rintro _ ⟨u, -, rfl⟩; exact hder u)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨z, rfl⟩
      have hz : (rho g.B (star a)).mulVec (z : Fin d → k) = 0 := by
        have := z.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      exact horth u z ((hu : (u : Fin d → k) ∈ Wd g.B a).2 z hz))
  rw [LinearMap.finrank_range_of_inj hT, ← (Submodule.equivMapOfInjective D hD W0).finrank_eq, hW0, hrk] at hc
  exact (pow_dvd_pow p (finrank_ker_rhoH_le g.B a)).trans hc

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropernessDescendsFgSubalgebra
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    pullback (i ≫ q) g ⟶ pullback q g :=
  pullback.lift (pullback.fst (i ≫ q) g ≫ i) (pullback.snd (i ≫ q) g)
    (by rw [Category.assoc, pullback.condition])

theorem baseChangeMap_snd {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.snd q g = pullback.snd (i ≫ q) g :=
  pullback.lift_snd _ _ _

theorem baseChangeMap_fst {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.fst q g = pullback.fst (i ≫ q) g ≫ i :=
  pullback.lift_fst _ _ _

theorem isPullback_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    IsPullback (baseChangeMap i q g) (pullback.fst (i ≫ q) g) (pullback.fst q g) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd q g) (h₂₂ := q) (v₁₃ := g) ?_
    (baseChangeMap_fst i q g) (IsPullback.of_hasPullback q g).flip
  rw [baseChangeMap_snd]
  exact (IsPullback.of_hasPullback (i ≫ q) g).flip

theorem range_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    Set.range (baseChangeMap i q g) = pullback.fst q g ⁻¹' Set.range i := by
  have h := isPullback_baseChangeMap i q g
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

theorem exists_fg_isProper_of_isQProjOver (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hp : IsQProjOver p)
    (hV : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨N, i, hi, -, rfl⟩ := hp
  have hq : IsProper (PSpace.str k N) := isProper_str k N

  have hcl : IsClosed (pullback.fst (PSpace.str k N) (spMap (algebraMap k V)) ⁻¹' Set.range i) := by
    rw [← range_baseChangeMap]
    have h1 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V)) ≫
        pullback.snd (PSpace.str k N) (spMap (algebraMap k V))) := by
      rw [baseChangeMap_snd]; exact hV
    have h2 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))) :=
      IsProper.of_comp _ (pullback.snd (PSpace.str k N) (spMap (algebraMap k V)))
    exact (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))).isClosedMap.isClosed_range
  obtain ⟨R, hR, hclR⟩ := exists_fg_isClosed_preimage_range k V X (PSpace k N) i (PSpace.str k N) hi inferInstance inferInstance hcl
  refine ⟨R, hR, ?_⟩
  rw [← range_baseChangeMap] at hclR
  have hb : IsImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    MorphismProperty.of_isPullback (P := @IsImmersion)
      (isPullback_baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))).flip hi
  have hc : IsClosedImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    IsClosedImmersion.of_isPreimmersion _ hclR
  rw [← baseChangeMap_snd]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
end

