module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeMultiplicationNorm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormula
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeRightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteKernelNonzero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsProper t.G.hom → ∀ (d : ℕ) (_ : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E), a ≠ 0 → (∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) ∧ ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → Module.finrank k A ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * d) :=
  PositivityTheory.Xgn.degree_multiplication_norm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlatHermHodgeCptConst
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_flatHerm_hodgeCpt_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 → (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) → (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) → OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ F' _ _ ψ A c₀ r cinf hR hA hB hC hc₀ hgen hZ hcinf hnorm
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  have hD := _root_.GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn E H D l Xo c O β Y S Ω K J y 𝔐 Fl xdeg e τ hR
  rw [← hA] at hD
  refine ⟨hO, _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_of_adelic K J Ω F' y ψ 𝔐.X 𝔐.ξ Ω _ (∏ i, e (τ, i)) c₀ A r cinf hO hB hC 𝔐.tie hN hD hc₀
    (fun p => ?_) hcinf hnorm⟩
  by_cases hp : p ∈ genFibre ℤ 𝔐.ξ
  · exact Or.inl ⟨cst_mem_regAt_of_genFibre hN ψ hp, orderAt_one_zero.2 (hgen p hp)⟩
  · obtain ⟨v, hv⟩ := exists_place_of_notMem_genFibre hN ψ hp
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F'
    obtain ⟨m, n, hm, hn, h⟩ := hZ v π hπ
    exact Or.inr ⟨v, π, m, n, hv, hπ, hm, hn, h p hv⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    GlobalTheory.CompanionTheory.Ar.dualMap φ = Formalism.L2.Pj.dualMap φ := by
  ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, Formalism.L2.Pj.dualMap]

theorem exists_frame_ring {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* T) (x : Sp T ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F T := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] T := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (FrameEig.isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (FrameEig.isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S T ψa z τ w.left h1 h2
  exact ⟨a, (FrameEig.isComb_iff a v w).2 ha, fun b hb => hu b ((FrameEig.isComb_iff b v w).1 hb)⟩


set_option backward.isDefEq.respectTransparency false in
theorem exists_localData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → centre (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) ∈ U → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.X) (_ : IsOpenImmersion x) (θ : R →+* (Localization.AtPrime q)) (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (C₁ : Matrix (Fin D.p) (Fin D.p) (Localization.AtPrime q)) (C₂ : Matrix (Fin D.q) (Fin D.q) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j ∧ spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j ∧ a = α • exteriorPower.ιMulti Z.Ω D.p b₁ ∧ b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ ∧ φ₂ f = α / κ ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) ∧ (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) ∧ (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) ∧ IsUnit C₁.det ∧ IsUnit C₂.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z a b S _ _ z q _ hp hq hgen hcen
  classical
  let T := Localization.AtPrime q
  let y : Sp T ⟶ Xo.XF c := spMap (algebraMap S T) ≫ zPt z
  let c₀ : c.F →+* T := (algebraMap S T).comp (algebraMap c.F S)
  have hy2 : y ≫ pullback.snd _ _ = spMap c₀ := by
    simp only [y, c₀, Category.assoc, zPt_snd, spMap, ← Spec.map_comp]
    rfl
  have hy1 : under y = spMap (algebraMap S T) ≫ z.x := by
    simp only [y, under, Category.assoc, zPt_fst]
  obtain ⟨h, κ, hκ₁, hκ₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef E H D l Xo c U O β Y Z T y c₀ hy2 hcen
  let P : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y ≫ Y.j), h⟩
  let x₀ := Y.X.fromSpecStalk P.1
  let θs : Y.X.presheaf.stalk P.1 →+* T := (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom
  have hθs : spMap θs ≫ x₀ = y ≫ Y.j := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hκ₂' : θs.comp κ = c₀ := hκ₂
  obtain ⟨r₁, e₁, he₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ τ
  obtain ⟨r₂, e₂, he₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ (ComplexEmbedding.conjugate τ)
  obtain ⟨V₁, hV₁, hVf₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ E H D l Xo c O β Y T y _ x₀ κ θs τ r₁ e₁ hθs he₁
  obtain ⟨V₂, hV₂, hVf₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ E H D l Xo c O β Y T y _ x₀ κ θs _ r₂ e₂ hθs he₂
  rw [hκ₂'] at hVf₁ hVf₂
  obtain ⟨u₁, hu₁, huf₁⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 τ D.p hp
  obtain ⟨u₂, hu₂, huf₂⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 (ComplexEmbedding.conjugate τ) D.q hq
  obtain ⟨hr₁, M₁, hM₁, M₁', hl₁, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₁ V₁ huf₁ hVf₁
  obtain ⟨hr₂, M₂, hM₂, M₂', hl₂, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₂ V₂ huf₂ hVf₂
  subst hr₁ hr₂
  obtain ⟨b₁, hbE₁, hbF₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig E H D l Xo c U O β Y Z P κ τ _ e₁ hκ₁ he₁
  obtain ⟨b₂, hbE₂, hbF₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig E H D l Xo c U O β Y Z P κ _ _ e₂ hκ₁ he₂
  have hP : P ∈ Z.genFib := by
    have key : ∀ t : Sp T, (y ≫ Y.j) t = pullback.fst Y.s (spMap β) (Y.jQ (y t)) := fun t => by
      simp only [Model.j, Scheme.Hom.comp_apply]
    exact ⟨Y.jQ (y (IsLocalRing.closedPoint T)), (key _).symm⟩
  obtain ⟨α, κ', ha, hb, s, hs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames Y.X Z.Ω _ Z.V _ _ _ _ a b P b₁ b₂ (hgen.2.2 P hP) hbF₁ hbF₂
  haveI := Y.t.semi.smooth
  obtain ⟨R, _, x, _, θA, e', f', -, hθA, hf', ht, hleft⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread Y.X Y.t.G P.1 (Fin D.p ⊕ Fin D.q)
    (Sum.elim e₁ e₂) s (by rintro (i | i); exacts [(hbE₁ i).1, (hbE₂ i).1])
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hθ : spMap (θs.comp θA) ≫ x = spMap (algebraMap S T) ≫ zPt z ≫ Y.j := by
    rw [hcomp, Category.assoc, hθA]
    exact hθs.trans (Category.assoc _ _ _)
  have hcε : ∀ i : Fin D.p ⊕ Fin D.q, spMap (Formalism.L2.Pj.dualMap θs) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (Formalism.L2.Pj.dualMap (θs.comp θA)) ≫ (e' i).left := fun i => by
    rw [hleft i, ← dualMap_eq, ← dualMap_eq, ← Category.assoc, LieVB.spMap_dual_comp]
  have hcγ : ∀ i : Fin D.p ⊕ Fin D.q, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA = (genMap (Z.ξ₀ ≫ Y.j) P).comp θA ∧
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap (Z.ξ₀ ≫ Y.j) P)) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((genMap (Z.ξ₀ ≫ Y.j) P).comp θA)) ≫ (e' i).left := fun i => ⟨rfl, by
    rw [hleft i, ← Category.assoc, LieVB.spMap_dual_comp]⟩
  refine ⟨R, inferInstance, x, inferInstance, θs.comp θA, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA, fun i => e' (Sum.inl i),
    fun j => e' (Sum.inr j), f', b₁, b₂, α, κ', M₁, M₂, hθ, ?_, ha, hb, ?_, fun i => ht _, fun j => ht _, ?_, ?_,
    Matrix.isUnit_det_of_right_inverse hl₁, Matrix.isUnit_det_of_right_inverse hl₂, ?_, ?_⟩
  · rw [hcomp, Category.assoc, hθA]
    exact LieTangent.spec_genMap _ P
  · change genMap (Z.ξ₀ ≫ Y.j) P (θA f') = α / κ'
    rw [hf']; exact hs
  · intro i
    rw [(hbE₁ i).2]
    exact (hcγ (Sum.inl i)).2
  · intro i
    rw [(hbE₂ i).2]
    exact (hcγ (Sum.inr i)).2
  · intro i
    refine ⟨(V₁ i).left, ?_, ?_⟩
    · have := hV₁ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₁ i).left = _ from hcε (Sum.inl i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₁ i) u₁ (V₁ i)).1 (hM₁ i)
      simpa only [hu₁] using this
  · intro i
    refine ⟨(V₂ i).left, ?_, ?_⟩
    · have := hV₂ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₂ i).left = _ from hcε (Sum.inr i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₂ i) u₂ (V₂ i)).1 (hM₂ i)
      simpa only [hu₂] using this

theorem spMap_field_pt {S F : Type} [CommRing S] [Field F] (ψ : S →+* F) (t : Sp F) :
    (spMap ψ) t = (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum S) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap ψ (t : PrimeSpectrum F).asIdeal = RingHom.ker ψ
  haveI := PrimeSpectrum.isPrime (t : PrimeSpectrum F)
  rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum F).asIdeal]
  rfl

theorem spMap_local_pt {S : Type} [CommRing S] (q : Ideal S) [hq : q.IsPrime] :
    (spMap (algebraMap S (Localization.AtPrime q))) (IsLocalRing.closedPoint (Localization.AtPrime q)) =
      (⟨q, hq⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext (by
    change Ideal.comap _ _ = q
    exact Localization.AtPrime.under_maximalIdeal)

theorem exists_regular_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ hτ hU hL hF p z k _ ψ₀ y₀ hy₁ hy₂ hy₃
  classical
  let q : Ideal p.R := RingHom.ker ψ₀
  haveI hqp : q.IsPrime := RingHom.ker_isPrime ψ₀
  have hy₀ : y₀ = spMap ψ₀ ≫ zPt z := eq_zPt z ψ₀ y₀ hy₁ hy₂
  have hmemU : zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ U := by
    obtain ⟨t⟩ : Nonempty (Sp k) := ⟨IsLocalRing.closedPoint k⟩
    have h := hy₃ ⟨t, rfl⟩
    rw [hy₀, Scheme.Hom.comp_apply, spMap_field_pt] at h
    exact h
  have hcen : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) ∈ U := by
    have key : ∀ t : Sp (Localization.AtPrime q), (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) t =
        zPt z ((spMap (algebraMap p.R (Localization.AtPrime q))) t) := fun t => by rw [Scheme.Hom.comp_apply]
    have e : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) = zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) :=
      (key _).trans (congrArg (zPt z) (spMap_local_pt q))
    rw [e]
    exact hmemU
  have hWo : IsOpen ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) := hU.isOpen.preimage (zPt z).continuous
  obtain ⟨_, ⟨gU, rfl⟩, hgU, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) from hmemU) hWo
  have hgU0 : ψ₀ gU ≠ 0 := hgU
  have hrange : ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x →
      y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ gU ≠ 0 → Set.range y ⊆ U := by
    rintro F _ ψ y h1 h2 hg _ ⟨t, rfl⟩
    rw [eq_zPt z ψ y h1 h2, Scheme.Hom.comp_apply, spMap_field_pt]
    exact hsub (show (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum p.R) ∈ PrimeSpectrum.basicOpen gU from hg)
  by_cases hpq : D.mult τ = D.p ∧ D.mult (ComplexEmbedding.conjugate τ) = D.q
  swap
  · exact ⟨gU, 0, hgU0, fun F _ ψ y h1 h2 hg => ⟨hrange F ψ y h1 h2 hg, fun v w hp hq => (hpq ⟨hp, hq⟩).elim⟩⟩
  obtain ⟨hp, hq⟩ := hpq
  obtain ⟨a, b, hgen, hrep⟩ := hF.exists_gen
  obtain ⟨R, _, x, _, θ, φ₂, e₁, e₂, f, b₁, b₂, α, κ, C₁, C₂, hθ, hφ₂, ha, hb, hf, ht₁, ht₂, hb₁, hb₂, hu₁, hu₂,
    hc₁, hc₂⟩ := exists_localData E H D l Xo c U τ O β Y Z a b p.R z q hp hq hgen hcen
  obtain ⟨g, θ', C₁', C₂', hgq, hθ', hu₁', hu₂', hc₁', hc₂'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames E H D l Xo c O β Y p.R z q R x θ τ _ _ _
    hp hq e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hu₁ hu₂ hc₁ hc₂
  have FS := _root_.GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point E H D l Xo c U τ O β Y Z φ a b p.R z hp hq R x φ₂ e₁ e₂ f b₁ b₂ α κ
    (Localization.Away g) θ' C₁' C₂' hL hrep hφ₂ ha hb hf ht₁ ht₂ hb₁ hb₂ hθ' hu₁' hu₂' hc₁' hc₂'
  obtain ⟨m, a₀, hm⟩ := IsLocalization.Away.surj g (θ' f * C₁'.det * ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g))
  have hg0 : ψ₀ g ≠ 0 := hgq
  refine ⟨g ^ (m + 1) * gU, a₀ * g * gU, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hg0) hgU0
  intro F _ ψ y h1 h2 hg
  rw [map_mul, map_pow] at hg
  have hg1 : ψ g ≠ 0 := fun h => hg (by rw [h]; simp)
  have hg2 : ψ gU ≠ 0 := right_ne_zero_of_mul hg
  have hr := hrange F ψ y h1 h2 hg2
  refine ⟨hr, fun v w hp' hq' hv hw => ?_⟩
  let ψ' : Localization.Away g →+* F := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hg1)
  have hψ : ψ'.comp (algebraMap p.R (Localization.Away g)) = ψ := IsLocalization.Away.lift_comp g _
  have hy : y = spMap ψ' ≫ spMap (algebraMap p.R (Localization.Away g)) ≫ zPt z := by
    rw [eq_zPt z ψ y h1 h2, ← Category.assoc]
    congr 1
    conv_lhs => rw [← hψ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have X := FS F ψ' y hy hr v w (by rw [hψ]; exact hv) (by rw [hψ]; exact hw)
  have hψa : ∀ s, ψ' (algebraMap p.R (Localization.Away g) s) = ψ s := fun s => RingHom.congr_fun hψ s
  have hinv : ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h3 := congrArg ψ' hm
  simp only [map_mul, map_pow, hψa] at h3
  have hφ : φ F y v w = ψ' (θ' f) * ψ' C₁'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) := by
    calc φ F y v w = φ F y v w * (ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g)) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, X]
  rw [hφ, map_mul, map_mul, map_mul, map_pow, ← h3]
  ring

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LiesOver

open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_add {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩

theorem valAt_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {w : (Σ k, J k) → ℂ}

theorem evC_xpow (w : (Σ k, J k) → ℂ) (c : ∀ k, J k) (e : K → ℕ) :
    evC w (ArakelovGeometry.xpow c e) = ∏ k, w ⟨k, c k⟩ ^ e k := by
  simp [evC, ArakelovGeometry.xpow, map_prod]

theorem exists_form_valAt (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing J), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k ∧
      ValAt ξ z x (evC w G / ∏ k, w ⟨k, c k⟩ ^ δ k) := by
  classical
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 := fun δ =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩
    · rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
      simp [div_mul_cancel₀ _ (hy k)]
    · obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
      have e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩ := by
        rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
        simp
      have e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩ := by simp [evC]
      rw [e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]
      exact hr
  | algebraMap r =>
    refine ⟨0, C r, isMultiHomog_C r, by simp, ?_⟩
    have e : evC w (C r : MRing J) = (r : ℂ) := by simp [evC]
    simp only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]
    simpa using valAt_int hz r
  | add a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add (f := _), map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
    · convert valAt_add u₁ u₂ using 1
      have e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) =
          evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁) := by
        simp only [evC, map_add (f := _), map_mul]
      rw [e, evC_xpow, evC_xpow, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩
    · rw [map_mul, v₁, v₂, hpow]
      ring
    · convert CoordModel.valAt_mul u₁ u₂ using 1
      have e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂ := by simp only [evC, map_mul]
      rw [e, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp

end Values

theorem valAt_cst : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a
  classical
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hO : OverInt y ψ := overInt_of_normalCpt ht hN ψ
  have hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F')) := by
    intro b
    obtain ⟨δ, G, hG, hv, hu⟩ := exists_form_valAt hz hw c hy hc (hO.2 c hy b)
    have h1 := hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by
      rw [hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])
    rw [evC_xpow] at h1
    have hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
    rwa [h1, mul_div_cancel_right₀ _ hW] at hu
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 := hint (⟨n • a, hi⟩ : 𝓞 F')
  have h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ) := valAt_int hz n
  obtain ⟨hn0, h3⟩ := CoordModel.valAt_inv h2
  have h4 := CoordModel.valAt_mul h3 h1
  convert h4 using 1
  · show ψ a = (n : Ω)⁻¹ * ψ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]
  · show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]

end GlobalTheory.CompanionTheory.Ar.Flat.LiesOver
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivOfSectionOfLocallyTriv
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem triv_of_section_of_locally_triv : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X), e ≫ p = 𝟙 S → (∀ U : S.Opens, IsIso (p.app U)) → ∀ M : LB X, M.IsLB → GlobalTheory.AbLaw.Triv (M.pull e) → (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ GlobalTheory.AbLaw.Triv (M.pull (p ⁻¹ᵁ U).ι)) → GlobalTheory.AbLaw.Triv M :=
  fun _ _ p e he hp _ hM h₀ loc =>
    GlobalTheory.CubeGlue.triv_of_locally_triv hM p e he (GlobalTheory.CubeGlue.surjective_restrict p hp) h₀ loc

end GlobalTheory.CompanionTheory.Ar.Approx
end

