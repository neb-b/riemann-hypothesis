module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetChangeOfBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inner_sum_left (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner (∑ l ∈ s, c l • u l) y = ∑ l ∈ s, (starRingEnd ℂ) (c l) * core.inner (u l) y := by
  classical
  have h0 : core.inner (0 : V) y = 0 := by
    have h := core.smul_left (0 : V) y 0
    simpa using h
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty]
    exact h0
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]

theorem inner_sum_right (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner y (∑ l ∈ s, c l • u l) = ∑ l ∈ s, core.inner y (u l) * c l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← core.conj_inner_symm, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Complex.conj_conj, core.conj_inner_symm, mul_comm]

theorem gram_change (core : InnerProductSpace.Core ℂ V) {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] (u : I → V) (w : J → V) (P : Matrix J I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    (Matrix.of fun a b => core.inner (w a) (w b)) =
      P.map (starRingEnd ℂ) * (Matrix.of fun a b => core.inner (u a) (u b)) * P.transpose := by
  ext a b
  rw [Matrix.of_apply, hw a, hw b, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left]
  simp only [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_right, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem norm_det_gram (core : InnerProductSpace.Core ℂ V) {I : Type} [Fintype I]
    [DecidableEq I] (u w : I → V) (P : Matrix I I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    ‖(Matrix.of fun a b => core.inner (w a) (w b)).det‖ =
      ‖P.det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (u a) (u b)).det‖ := by
  have hconj : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := by
    rw [RingHom.map_det]
    rfl
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.gram_change core u w P hw, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hconj, norm_mul, norm_mul, Complex.norm_conj]
  ring

noncomputable def blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => ℂ)
      (Fin.lastCases (motive := fun _ => ℂ) s d l)
      (fun j => Fin.lastCases (motive := fun _ => ℂ) 0 (C j) l) i

theorem det_blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    (blockMat C d s).det = s * C.det := by
  have hsub : (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = C := by
    ext i j
    simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat, Fin.succAbove_last]
  have hsign : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub, hsign, _root_.one_mul]
  simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot in
theorem GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (n : ℕ)
    (β : Fin (n + 1) → V) (x : Fin n → V) (xe : V) (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ),
    (∀ j, x j = ∑ l, C j l • β l.castSucc) → xe = ∑ l, d l • β l.castSucc + s • β (Fin.last n) → s ≠ 0 →
    (Matrix.of fun a b => core.inner (x a) (x b)).det ≠ 0 → (Matrix.of fun a b => core.inner (β a) (β b)).det ≠ 0 →
    (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ - Real.log ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖) =
      Real.log ‖s‖ + (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ -
        Real.log ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖) := by
  intro V _ _ core n β x xe C d s hx hxe hs hGx hGβ
  have hy : ∀ j, (Fin.snoc x xe : Fin (n + 1) → V) j = ∑ l, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s j l • β l := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, hxe, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
    · rw [Fin.snoc_castSucc, hx i, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
  have h1 : ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ =
      ‖(GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core β _ (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s) hy
  have h2 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ =
      ‖C.det‖ ^ 2 * ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core (fun l => β l.castSucc) x C hx
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.det_blockMat] at h1
  have hx0 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGx
  have hC : ‖C.det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h]
    simp
  have hβ' : ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h, mul_zero]
  have hβ : ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGβ
  have hs' : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  rw [h1, h2, norm_mul, mul_pow,
    Real.log_mul (mul_ne_zero (pow_ne_zero 2 hs') (pow_ne_zero 2 hC)) hβ,
    Real.log_mul (pow_ne_zero 2 hs') (pow_ne_zero 2 hC), Real.log_mul (pow_ne_zero 2 hC) hβ',
    Real.log_pow, Real.log_pow]
  push_cast
  ring
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FrameRebase

def sabRebase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' :=
  h ▸ m

theorem sabRebase_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') :
    (sabRebase m h).φ = m.φ := by
  subst h; rfl

theorem tied_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' _ _ _ h4 h5 h6 h7 _ _ _ _
  have hπ : A'.ξ ≫ (e.hom ≫ A.f) = x ≫ Y.j := by rw [← Category.assoc, h4, h5]
  obtain ⟨t, t', tΩ, a, a', m, m', u, u', E1, E2, E3⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist E H D l Xo c O O' β β' Y Y' g Φ n A'.X (e.hom ≫ A.f) A'.f Ω A'.ξ x x' hπ h6 h7
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t A.t t A.f e.hom A.m a
  obtain ⟨k', hk'⟩ := sabCancel pullCubCancel E H _ _ _ Y'.t A'.t t' A'.f (𝟙 _) A'.m
    (sabRebase a' (Category.id_comp A'.f).symm)
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ A.t t tΩ e.hom A'.ξ k m
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ A'.t t' (twistSAB tΩ g) (𝟙 _) A'.ξ k' m'
  let mA : SABMap tΩ A.t A.ξ := sabRebase n₁ h4
  let mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ := sabRebase n₂ (Category.comp_id _)
  have hmA : mA.φ = m.φ ≫ k.φ := (sabRebase_φ n₁ h4).trans hn₁
  have hmA' : mA'.φ = m'.φ ≫ k'.φ := (sabRebase_φ n₂ _).trans hn₂
  rw [sabRebase_φ] at hk'
  obtain ⟨M₁, P1, P2, -, P4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M h4
  obtain ⟨M₂, Q⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main A'.X Ω A'.ξ t.G A'.t.G tΩ.G m.φ mA'.φ m.cart mA'.cart A.Li M₁
  obtain ⟨φ, hφ, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₂ A'.M
  refine ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, ?_, ?_, E3, P1, ?_, P2, P4⟩
  · rw [hmA, Category.assoc, ← hk, E1]
  · rw [hmA', Category.assoc, ← hk', E2]
  · intro v
    obtain ⟨w, hw1, hw2⟩ := Q v
    exact ⟨w, hw1, by rw [hφ v]; exact hw2⟩

end GlobalTheory.CompanionTheory.Ar.FrameRebase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagOutsidePrimeFibres
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0

open HodgeChar0

theorem ht_eq_dR_of_not_inFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (p : ℕ), p ∈ S → ∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) →
      𝔐.HT p s q = 𝔐.dR s q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp s q hq
  classical
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  haveI hchar : CharZero Ω := charZero_of_injective_ringHom hcst
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint := _root_.GlobalTheory.CompanionTheory.Ar.isInternal_eigSp Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  have htop : (⨆ s, 𝔐.Vgen s) = ⊤ := hint.submodule_iSup_eq_top
  have hind : iSupIndep 𝔐.Vgen := hint.submodule_iSupIndep
  have hreg : ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := fun s a q =>
    HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom)
  have hnat := unitAt_natCast (q := q) hq
  have hV : ∀ s, 𝔐.V s q = 𝔐.dR s q := fun s =>
    Lat.patch_of_not S _ _ fun p hp => hq p (𝔐.S_prime p hp)
  have hint' : ∀ (s : CMType H ⊕ CMType H) a, IsIntegral ℤ (𝔐.emb s a) := fun s a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom
  have hsep : ∀ s t, s ≠ t → ∃ a, 𝔐.emb s a ≠ 𝔐.emb t a ∧ (𝔐.emb s a - 𝔐.emb t a)⁻¹ ∈ regAt 𝔐.ξ q := by
    intro s t hst
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (fun e => hst (hinj e))
    exact ⟨a, ha, inv_mem_regAt hnat (sub_mem (hreg s a q) (hreg t a q)) ((hint' s a).sub (hint' t a))⟩
  have hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
    refine le_antisymm (fun e he => ?_) (iSup_le fun s => inf_le_left)
    have he' : e ∈ ⨆ s, 𝔐.Vgen s := by rw [htop]; trivial
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 he'
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at he ⊢
    have h1 := mem_of_sum_mem (𝔐.M.lat q) 𝔐.ρ 𝔐.emb
      (fun a e he => lat_stable 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act q a he) (fun s a => hreg s a q) hsep Finset.univ f
      (fun s _ => hf s) he
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.mem_iSup_of_mem s ⟨h1 s (Finset.mem_univ s), hf s⟩
  have hbi : ∀ x, (∀ w ∈ 𝔐.M.omLat q, w x ∈ regAt 𝔐.ξ q) → x ∈ 𝔐.M.lat q := by
    intro x hx
    choose U hU b hb hfr using fun s => 𝔐.vb s q trivial
    rw [hlat]
    refine mem_iSup_of_dual 𝔐.Vgen hind htop (labelRk D) b (fun s => (hfr s q trivial (hU s)).1) hb
      (fun s => 𝔐.dR s q) (fun s => (hV s).symm.trans (hfr s q trivial (hU s)).2) x fun w hw =>
        hx w (show ∀ e ∈ 𝔐.M.lat q, w e ∈ regAt 𝔐.ξ q from fun e he => by
          rw [hlat] at he
          exact Submodule.iSup_induction _ (motive := fun e => w e ∈ regAt 𝔐.ξ q) he hw
            (by simpa using zero_mem _) (fun a b ha hb => by simpa using add_mem ha hb))
  have hpp : p.Prime := 𝔐.S_prime p hp
  have hn : unitAt 𝔐.ξ q ((p ^ 𝔐.R p : ℕ) : Ω) := hnat _ (pow_ne_zero _ hpp.ne_zero)
  have hd : ∀ s, 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q = 𝔐.dR s q := fun s =>
    htDual_eq_eigLat 𝔐.M 𝔐.ρ _ 𝔐.t.PP.isLB hn hbi
  cases s with
  | inl τ =>
    have hbot : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
    exact htW_eq_eigLat 𝔐.M 𝔐.ρ _ (hd _) (fun d => hreg _ d q) _ (Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
      (Ideal.absNorm_mem _) (hnat _ (by simpa [Ideal.absNorm_eq_zero_iff] using hbot))
  | inr τ => exact hd _

end GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ImmBlock

theorem aeval_mul_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommRing R] {alg : Algebra ℤ R}
    {F : MvPolynomial σ ℤ} {n : ℕ}
    (hF : F.IsHomogeneous n) (a : σ → R) (t : R) :
    MvPolynomial.aeval (fun i => a i * t) F = MvPolynomial.aeval a F * t ^ n := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    have h2 : Finsupp.degree d = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h2, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, _root_.mul_assoc]

theorem aeval_ringHom {σ A B : Type*} [CommRing A] [CommRing B] {algA : Algebra ℤ A} {algB : Algebra ℤ B}
    (φ : A →+* B) (a : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun i => φ (a i)) P = φ (MvPolynomial.aeval a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem differentiable_aeval {σ κ : Type*} [Fintype κ] (g : σ → κ) (P : MvPolynomial σ ℤ) :
    Differentiable ℂ (fun u : κ → ℂ => MvPolynomial.aeval (fun i => u (g i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (differentiable_apply _)

theorem form_mem {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (k₀ k : K) (n : ℕ) (F G : MvPolynomial (J k₀) ℤ) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous n) (c d : J k)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) G * y ⟨k, d⟩) :
    MvPolynomial.rename (Sigma.mk k₀) F * MvPolynomial.X ⟨k, c⟩ -
      MvPolynomial.rename (Sigma.mk k₀) G * MvPolynomial.X ⟨k, d⟩ ∈ mCoordIdeal y := by
  have hh := congrArg (MvPolynomial.C : Ω → MvPolynomial K Ω) h
  simp only [map_mul] at hh
  rw [mCoordIdeal, RingHom.mem_ker]
  simp only [mConeMap, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def]
  rw [aeval_mul_of_isHomogeneous hF (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_mul_of_isHomogeneous hG (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) F,
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) G]
  linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * hh

theorem differentiableAt_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ} {v : E}
    (ha : DifferentiableAt ℂ a v) (hb : DifferentiableAt ℂ b v) (h : b v ≠ 0) :
    DifferentiableAt ℂ (fun w => a w / b w) v := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv h)

theorem ker_bot_of_factor {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {f : E → F₁} {a : E → F₂} {Ψ : F₁ → F₂} {v₀ : E}
    (hf : DifferentiableAt ℂ f v₀) (hΨ : DifferentiableAt ℂ Ψ (f v₀)) (h : a =ᶠ[nhds v₀] Ψ ∘ f)
    (hk : (fderiv ℂ a v₀).ker = ⊥) : (fderiv ℂ f v₀).ker = ⊥ := by
  rw [h.fderiv_eq, fderiv_comp v₀ hΨ hf] at hk
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ f v₀ u = 0 := hu
  have : u ∈ ((fderiv ℂ Ψ (f v₀)).comp (fderiv ℂ f v₀)).ker := by
    change (fderiv ℂ Ψ (f v₀)) (fderiv ℂ f v₀ u) = 0
    rw [hu', map_zero]
  rwa [hk] at this

theorem immersion_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  intro X Ω _ _ ξ K _ J _ y k₀ hTie hEmb e M _ A U lam hE κ _ ix x p hp j hj
  classical
  have hev : ∀ (z : (Σ k, J k) → ℂ) (f : MRing J),
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := fun z f => by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  set G : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun v => lam x ((A.chart j).symm v) with hGdef
  set v₀ : Fin e → ℂ := A.chart j x with hv₀
  have hG0 : G v₀ = lam x x := by
    simp only [hGdef, hv₀]
    rw [(A.chart j).left_inv hj]
  have hS : v₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    change (A.chart j).symm (A.chart j x) ∈ U x
    rw [(A.chart j).left_inv hj]
    exact hE.mem_U x
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U x) :=
    (A.chart j).isOpen_inter_preimage_symm (hE.isOpen x)
  have hAn : ∀ q, DifferentiableAt ℂ (fun v => G v q) v₀ := fun q =>
    (hE.holo x q j v₀ hS).differentiableAt
  have hCo : ∀ q, ContinuousAt (fun v => G v q) v₀ := fun q => (hAn q).continuousAt
  have hw : lam x x ∈ mcPts (mCoordIdeal y) := hE.mem x x (hE.mem_U x)
  have hwpts : lam x x ∈ Small.ptsOver ℂ (mCoordIdeal y) :=
    ⟨hw.1, fun f hf => by rw [← hev]; exact hw.2 f hf⟩
  choose r hr using hw.1
  set p' : (k : K) → J k := Function.update r k₀ (ix p) with hp'def
  have hp'0 : p' k₀ = ix p := by simp [hp'def]
  have hp' : ∀ k, lam x x ⟨k, p' k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hp'0]
      exact hp
    · rw [hp'def, Function.update_of_ne h]
      exact hr k
  have hblk := fun k => _root_.GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms X Ω ξ K J y k₀ hTie hEmb ℂ (lam x x) hwpts (ix p) k (p' k) hp (hp' k)
  choose n F hFh hFr hFn using hblk

  set f : (Fin e → ℂ) → κ → ℂ := fun v i => G v ⟨k₀, ix i⟩ / G v ⟨k₀, ix p⟩ with hfdef
  have ht0 : G v₀ ⟨k₀, ix p⟩ ≠ 0 := by rw [hG0]; exact hp
  have hfd : DifferentiableAt ℂ f v₀ :=
    by
    refine differentiableAt_pi.2 fun i => ?_
    have h := differentiableAt_quot (hAn ⟨k₀, ix i⟩) (hAn ⟨k₀, ix p⟩) ht0
    exact h

  set ev : MvPolynomial (J k₀) ℤ → (κ → ℂ) → ℂ :=
    fun P u => MvPolynomial.aeval (fun i' : J k₀ => u (ix.symm i')) P with hevdef
  have hevd : ∀ P, Differentiable ℂ (ev P) := fun P => differentiable_aeval (fun i' => ix.symm i') P
  have hscale : ∀ v k (d : J k), ev (F k d) (f v) =
      MvPolynomial.aeval (fun i' : J k₀ => G v ⟨k₀, i'⟩) (F k d) * ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k := by
    intro v k d
    rw [← aeval_mul_of_isHomogeneous (hFh k d)]
    simp only [hevdef, hfdef, Equiv.apply_symm_apply, div_eq_mul_inv]
  have hden0 : ∀ k, ev (F k (p' k)) (f v₀) ≠ 0 := by
    intro k
    rw [hscale, hG0]
    exact mul_ne_zero (hFn k) (pow_ne_zero _ (inv_ne_zero hp))
  set Ψ : (κ → ℂ) → (Σ k, J k) → ℂ := fun u q => ev (F q.1 q.2) u / ev (F q.1 (p' q.1)) u with hΨdef
  have hΨd : DifferentiableAt ℂ Ψ (f v₀) :=
    by
    refine differentiableAt_pi.2 fun q => ?_
    have h := differentiableAt_quot (hevd (F q.1 q.2) (f v₀)) (hevd (F q.1 (p' q.1)) (f v₀)) (hden0 q.1)
    exact h

  have e1 : ∀ᶠ v in nhds v₀, G v ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hSo.mem_nhds hS] with v hv
    exact hE.mem x _ hv.2
  have e2 : ∀ᶠ v in nhds v₀, ∀ k, G v ⟨k, p' k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (hCo ⟨k, p' k⟩).eventually_ne (by rw [hG0]; exact hp' k)
  have e3 : ∀ᶠ v in nhds v₀, ∀ k, ev (F k (p' k)) (f v) ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (((hevd _).continuous.continuousAt).comp hfd.continuousAt).eventually_ne (hden0 k)
  have e4 : ∀ᶠ v in nhds v₀, G v ⟨k₀, ix p⟩ ≠ 0 := (hCo _).eventually_ne ht0
  have hfac : (fun v => affCoord p' (G v)) =ᶠ[nhds v₀] Ψ ∘ f := by
    filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
    funext q
    obtain ⟨k, d⟩ := q
    have hmem := form_mem y k₀ k (n k) (F k d) (F k (p' k)) (hFh k d) (hFh k (p' k)) (p' k) d (hFr k d)
    have h0 := h1.2 _ hmem
    rw [hev] at h0
    simp only [map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def] at h0
    have hrel : ev (F k d) (f v) * G v ⟨k, p' k⟩ = ev (F k (p' k)) (f v) * G v ⟨k, d⟩ := by
      rw [hscale, hscale]
      linear_combination ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k * h0
    change G v ⟨k, d⟩ / G v ⟨k, p' k⟩ = ev (F k d) (f v) / ev (F k (p' k)) (f v)
    rw [div_eq_div_iff (h2 k) (h3 k)]
    linear_combination -hrel
  have hk : (fderiv ℂ (fun v => affCoord p' (G v)) v₀).ker = ⊥ :=
    hE.immersion x p' hp' j hj
  exact ⟨hfd, ker_bot_of_factor hfd hΨd hfac hk⟩

end GlobalTheory.CompanionTheory.Ar.ImmBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem saStatement_holds : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := PositivityTheory.EqVol.sa

end GlobalTheory.CompanionTheory.Ar.Link
end

