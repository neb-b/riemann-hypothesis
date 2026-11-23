module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IteratedDerivativeFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

namespace GlobalTheory.CompanionTheory.Ar.JetLeib

theorem jet_mul_first {u v : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) (i : ℕ)
    (h0 : ∀ k < i, iteratedDeriv k u 0 = 0) :
    (∀ k < i, iteratedDeriv k (fun t => u t * v t) 0 = 0) ∧
      iteratedDeriv i (fun t => u t * v t) 0 = v 0 * iteratedDeriv i u 0 := by
  have key : ∀ n : ℕ, iteratedDeriv n (fun t => u t * v t) 0 =
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℂ) * iteratedDeriv m u 0 * iteratedDeriv (n - m) v 0 := fun n =>
    iteratedDeriv_fun_mul hu.contDiffAt hv.contDiffAt
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [key k]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk : m < i := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hk
    rw [h0 m hmk]
    simp
  · rw [key i, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp [mul_comm]
    · intro m hm
      rw [h0 m (Finset.mem_range.mp hm)]
      simp

theorem jet_first_nonzero : ∀ (r : ℕ) (Ψ : Fin r → ℂ → ℂ) (c : Fin r → ℂ) (h F : ℂ → ℂ), (∀ j, AnalyticAt ℂ (Ψ j) 0) → AnalyticAt ℂ F 0 → F 0 ≠ 0 → (∀ᶠ τ in 𝓝 (0 : ℂ), ∑ j, c j * Ψ j τ = h τ * F τ) → ∀ i : ℕ, ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) ↔ ∀ k < i, iteratedDeriv k h 0 = 0) ∧ ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) → ∑ j, c j * iteratedDeriv i (Ψ j) 0 = F 0 * iteratedDeriv i h 0) := by
  intro r Ψ c h F hΨ hF hF0 hev i
  have hP : AnalyticAt ℂ (fun τ => ∑ j, c j * Ψ j τ) 0 :=
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (hΨ j)
  have hDP : ∀ k : ℕ, iteratedDeriv k (fun τ => ∑ j, c j * Ψ j τ) 0 =
      ∑ j, c j * iteratedDeriv k (Ψ j) 0 := by
    intro k
    have hc : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        ContDiffAt ℂ k (fun τ => c j * Ψ j τ) 0 := fun j _ =>
      (analyticAt_const.mul (hΨ j)).contDiffAt
    rw [iteratedDeriv_fun_sum (f := fun j τ => c j * Ψ j τ) hc]
    exact Finset.sum_congr rfl fun j _ => iteratedDeriv_const_mul_field (c j) (Ψ j)
  have hFi : AnalyticAt ℂ (fun t => (F t)⁻¹) 0 := hF.inv hF0
  have hne : ∀ᶠ τ in 𝓝 (0 : ℂ), F τ ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hh : h =ᶠ[𝓝 (0 : ℂ)] fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹ := by
    filter_upwards [hev, hne] with τ h1 h2
    rw [h1, _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.mul_one]
  have hha : AnalyticAt ℂ h 0 := (hP.mul hFi).congr hh.symm
  have hPe : (fun τ => ∑ j, c j * Ψ j τ) =ᶠ[𝓝 (0 : ℂ)] fun t => h t * F t := hev
  have hDPh : ∀ k : ℕ, ∑ j, c j * iteratedDeriv k (Ψ j) 0 =
      iteratedDeriv k (fun t => h t * F t) 0 := fun k => by
    rw [← hDP k]; exact hPe.iteratedDeriv_eq k
  have hDh : ∀ k : ℕ, iteratedDeriv k h 0 =
      iteratedDeriv k (fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹) 0 := fun k =>
    hh.iteratedDeriv_eq k
  have back : (∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) →
      ∀ k < i, iteratedDeriv k h 0 = 0 := by
    intro hz k hk
    rw [hDh k]
    exact (jet_mul_first hP hFi i fun k hk => by rw [hDP k]; exact hz k hk).1 k hk
  refine ⟨⟨back, fun hz k hk => ?_⟩, fun hz => ?_⟩
  · rw [hDPh k]
    exact (jet_mul_first hha hF i hz).1 k hk
  · rw [hDPh i]
    exact (jet_mul_first hha hF i (back hz)).2

end GlobalTheory.CompanionTheory.Ar.JetLeib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem aug_comp_inL (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B).comp
        ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      (algebraMap k B).comp ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have h0 : (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.C a) : Jet k Unit p) =
        algebraMap k (Jet k Unit p) a := rfl
    simp only [RingHom.comp_apply, h0, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply k B (Jet B Unit p), AlgHom.commutes]
    rfl
  · intro i
    have h1 : (inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = dQ B p := by
      change (MvPolynomial.aeval fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    have h2 : (jetAug : Jet B Unit p →ₐ[B] B) (dQ B p) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : B)) (MvPolynomial.X () : MvPolynomial Unit B) = _
      simp
    have h3 : (jetAug : Jet k Unit p →ₐ[k] k)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : k)) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    simp only [RingHom.comp_apply, RingHom.coe_coe, h1, h2, h3, map_zero]

theorem red_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  intro E _ _ _ H X0 t k _ x p y B _ _ hy τ hτ j₀ hj₀
  have h1 : ∀ (κ : Fin 2) (q : Sp (Jet B Unit p)),
      (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) ≫
        (![y.left, (1 : Tm x p ⟶ t.G).left] : Fin 2 → _) κ) q ∈ t.PP.L.U j₀ := by
    intro κ q
    rw [Scheme.Hom.comp_apply]
    fin_cases κ
    · exact jet_left_mem t x j₀ hj₀ y hy _
    · exact jet_left_mem t x j₀ hj₀ 1 (by simp [Hom.one_def]) _
  have hc : spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫
        spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      spMap (algebraMap k B) ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [aug_comp_inL]
  obtain ⟨e₀, he, hall⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k Unit p)) t.PP.L t.PP.isLB B p (Fin 2)
    ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1] τ
    (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) j₀ h1
    (fun z' J' hG _ => by rw [hc]; exact hτ _ _ z' J' hG)
  exact ⟨e₀, he, fun z J hG hJ => hall z J hG fun κ => hJ _ (h1 κ z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_section_difference_generator : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | exact GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedDegreeGramDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree


open scoped ComplexOrder in
theorem gramDet_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ)
    {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem normDegree_top_eq_mean_gramDet : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  intro L _ _ B n e hli hspan
  let s : Fin n → (⊤ : Submodule (𝓞 L) B.carrier) := fun i => ⟨e i, Submodule.mem_top⟩
  have hs : LinearIndependent (𝓞 L) s :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 L) B.carrier).subtype hli
  have hcard : Fintype.card (Fin n) = B.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top,
      Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge), Fintype.card_fin]
  have hsp : Submodule.span (𝓞 L) (Set.range s) = ⊤ := by
    have hmap : (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := hx'
    exact hy
  have hone : Nat.card ((⊤ : Submodule (𝓞 L) B.carrier) ⧸ Submodule.span (𝓞 L) (Set.range s)) = 1 := by
    rw [hsp]
    exact Nat.card_unique
  have hg : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun i => ((s i : (⊤ : Submodule (𝓞 L) B.carrier)) : B.carrier)) = ‖B.gramDet σ e‖ :=
    fun σ => gramDet_eq_norm B σ hli
  rw [HermitianBundle.normDegree, B.degree_eq_of_linearIndependent ⊤ hs hcard,
    hone, Nat.cast_one, Real.log_one, zero_sub, mean]
  simp only [hg]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom

theorem exists_den {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (φ : R →+* A) {f : A} (hf : f ≠ 0) (T : Set (R × R × A))
    (hT : ∀ q ∈ T, q.2.1 ≠ 0 ∧ φ q.2.1 * q.2.2 = φ q.1 * f) :
    ∃ D : R, D ≠ 0 ∧ ∀ q ∈ T, φ q.2.1 ∣ φ (D * q.1) := by
  classical
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    ((fun q : R × R × A => q.2.2) '' T)).1
    (IsNoetherian.noetherian (Ideal.span ((fun q : R × R × A => q.2.2) '' T)))
  have hex : ∀ g ∈ s, ∃ q ∈ T, q.2.2 = g := fun g hg => by
    obtain ⟨q, hq, rfl⟩ := hsS hg
    exact ⟨q, hq, rfl⟩
  choose! q hqT hqg using hex
  refine ⟨∏ g ∈ s, (q g).2.1, Finset.prod_ne_zero_iff.2 fun g hg => (hT _ (hqT g hg)).1, ?_⟩
  set D := ∏ g ∈ s, (q g).2.1 with hD
  have key : ∀ a ∈ Submodule.span A (s : Set A), ∃ b, φ D * a = b * f := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg =>
      have hg' : g ∈ s := hg
      refine ⟨φ (∏ g' ∈ s.erase g, (q g').2.1) * φ (q g).1, ?_⟩
      have e := (hT _ (hqT g hg')).2
      rw [hqg g hg'] at e
      rw [hD, ← Finset.prod_erase_mul s _ hg', map_mul, _root_.mul_assoc, e, _root_.mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [mul_add, ha', hb', add_mul]⟩
    | smul c a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      refine ⟨c * a', ?_⟩
      rw [smul_eq_mul, mul_left_comm, ha', _root_.mul_assoc]
  intro r hr
  obtain ⟨b, hb⟩ := key r.2.2 (by
    rw [← hs]
    exact Ideal.subset_span ⟨r, hr, rfl⟩)
  refine ⟨b, mul_right_cancel₀ hf ?_⟩
  have e := (hT r hr).2
  calc φ (D * r.1) * f = φ D * (φ r.1 * f) := by rw [map_mul, _root_.mul_assoc]
    _ = φ r.2.1 * (φ D * r.2.2) := by rw [← e, mul_left_comm]
    _ = φ r.2.1 * b * f := by rw [hb, _root_.mul_assoc]

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}}

theorem f_ne_zero [IsIntegral X] {p : X ⟶ Sp R} {M : LB X} {t : SecMod p M} {i j : M.ι}
    (hi : LB.Sec.f t i ≠ 0) (hj : (M.U j : Set X).Nonempty) : LB.Sec.f t j ≠ 0 := by
  intro h0
  have hine : (M.U i : Set X).Nonempty := by
    by_contra hc
    have hb : M.U i = ⊥ := by
      ext x
      simp only [Set.not_nonempty_iff_eq_empty] at hc
      simp [hc]
    have : Subsingleton Γ(X, M.U i) := by
      rw [hb]
      infer_instance
    exact hi (Subsingleton.elim _ _)
  have hne : ((M.U i ⊓ M.U j : X.Opens) : Set X).Nonempty :=
    nonempty_preirreducible_inter (M.U i).isOpen (M.U j).isOpen hine hj
  have : Nonempty (M.U i ⊓ M.U j : X.Opens) := hne.to_subtype
  have e := LB.Sec.compat t i j
  rw [h0, map_zero, MulZeroClass.mul_zero] at e
  refine hi (map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) ?_)
  exact e.trans (map_zero _).symm

theorem exists_den_open [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp R) (M : LB X) (t : SecMod p M) (j : M.ι)
    (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) (hVj : V ≤ M.U j) (ht : LB.Sec.f t j ≠ 0) :
    ∃ D : R, D ≠ 0 ∧ ∀ (x d : R) (u : SecMod p M), d ≠ 0 → d • u = x • t →
      constHom p V d ∣ constHom p V (D * x) := by
  have : Nonempty V := hne.to_subtype
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let r := (X.presheaf.map (homOfLE hVj).op).hom
  have hinj : Function.Injective r := map_injective_of_isIntegral X (homOfLE hVj)
  obtain ⟨D, hD, h⟩ := exists_den (constHom p V) (f := r (LB.Sec.f t j))
    (fun h0 => ht (hinj (by rw [map_zero]; exact h0)))
    {q | q.2.1 ≠ 0 ∧ constHom p V q.2.1 * q.2.2 = constHom p V q.1 * r (LB.Sec.f t j)} fun q hq => hq
  refine ⟨D, hD, fun x d u hd e => h (x, d, r (LB.Sec.f u j)) ⟨hd, ?_⟩⟩
  have e' := congrArg r (congrArg (fun s : SecMod p M => LB.Sec.f s j) e)
  simp only [smul_f, r, map_mul, res_constFn] at e'
  exact e'

theorem dvd_of_forall_point (p : X ⟶ Sp R) [Flat p] (hp : Function.Surjective p) {a b : R} (ha : a ≠ 0)
    (h : ∀ y : X, cst p y a ∣ cst p y b) : a ∣ b := by
  have hh : ∀ z ∈ (⊤ : (Sp R).Opens), cst (𝟙 (Sp R)) z a ∣
      gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
    intro z _
    obtain ⟨y, rfl⟩ := hp z
    apply dvd_descend p y
    rw [cst, ← gs_stalkMap p y ⊤ trivial, ← gs_stalkMap p y ⊤ trivial]
    exact h y
  obtain ⟨g, hg⟩ := exists_div (𝟙 (Sp R)) ha ⊤ _ hh
  have e : constFn (𝟙 (Sp R)) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
    have e₀ : (𝟙 (Sp R) : Sp R ⟶ Sp R).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Sp R).presheaf.map_id _
    rw [constFn, e₀]
    rfl
  rw [e] at hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g, ?_⟩
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hg
  simpa using this

theorem bounded_denominators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB →
    ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t →
      d ∣ d₀ * x := by
  classical
  intro R _ _ _ G _ _ _ _ M hM t ht
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hsurj : Function.Surjective G.hom := (inferInstance : Surjective G.hom).surj
  obtain ⟨i₀, hi₀⟩ : ∃ i, LB.Sec.f t i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ht (SecMod.ext fun i => by rw [hc i]; rfl)
  have hc : ∀ y : G.left, ∃ j, y ∈ M.U j := fun y => by
    have : y ∈ (⨆ i, M.U i : G.left.Opens) := by rw [hM.cover]; trivial
    simpa using this
  choose j hj using hc
  have hV : ∀ y : G.left, ∃ V : G.left.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ M.U (j y) := fun y => by
    obtain ⟨V, hVa, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (hj y)
    exact ⟨V, hVa, hy, hle⟩
  choose V hVa hVy hVj using hV
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun y => (V y : Set G.left))
    (fun y => (V y).isOpen.mem_nhds (hVy y))
  have hD := fun y => exists_den_open G.hom M t (j y) (V y) (hVa y) ⟨y, hVy y⟩ (hVj y)
    (f_ne_zero hi₀ ⟨y, hj y⟩)
  choose D hD0 hD using hD
  refine ⟨∏ y ∈ s, D y, Finset.prod_ne_zero_iff.2 fun y _ => hD0 y, fun x d u hd e => ?_⟩
  refine dvd_of_forall_point G.hom hsurj hd fun y => ?_
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ s, y ∈ V w := by
    have : y ∈ ⋃ x ∈ s, (V x : Set G.left) := by rw [hs]; trivial
    simpa using this
  have h₁ : constHom G.hom (V w) d ∣ constHom G.hom (V w) ((∏ y ∈ s, D y) * x) := by
    refine (hD w x d u hd e).trans (map_dvd _ ?_)
    exact mul_dvd_mul_right (Finset.dvd_prod_of_mem _ hw) _
  obtain ⟨c, hc⟩ := h₁
  have e' := congrArg (gs (𝟙 G.left) y (V w)) hc
  rw [constHom_apply, constHom_apply, gs_mul _ y _ hyw, gs_constFn _ _ _ y hyw, gs_constFn _ _ _ y hyw,
    Category.id_comp] at e'
  exact ⟨_, e'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom
end
end

