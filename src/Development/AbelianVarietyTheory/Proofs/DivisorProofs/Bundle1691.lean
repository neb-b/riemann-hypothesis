module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGLOfExhaustion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealIntegralTrivAtPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_trivAt_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (ℓ : ℕ), ℓ.Prime → Λ.TrivAt ℓ → ∀ la : HeightOneSpectrum (𝓞 c.F), (ℓ : 𝓞 c.F) ∈ la.asIdeal → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → la.valuation c.F s ≤ 1 := by
  intro E _ _ _ H Dw l c n Λ ℓ hℓ hT la hla s hs
  obtain ⟨k, hk, hkLa, hkstd⟩ := hT
  set w := la.valuation c.F with hwdef
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => hw ⟨x, hx⟩
  have hk1 : w (k : c.F) = 1 := by
    have h := (la.valuation_eq_one_iff_notMem (K := c.F) (r := (k : 𝓞 c.F))).2 ?_
    · simpa using h
    · intro hm
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 c.F) hk)
      have : (1 : 𝓞 c.F) ∈ la.asIdeal := by
        rw [← hab]
        exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hm) (la.asIdeal.mul_mem_left _ hla)
      exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hkv : ∀ τ : E →+* ℂ, w (embF c τ (k : E)) = 1 := fun τ => by rw [map_natCast]; exact hk1
  have hsm : ∀ v : Fin n → Fin n → E,
      (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) • Matrix.of fun i j => v j i := by
    intro v; ext i j; simp [Algebra.smul_def]
  have hdetk : ∀ v : Fin n → Fin n → E,
      Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • v j) i) = (k : E) ^ n * Matrix.det (Matrix.of fun i j => v j i) := by
    intro v; rw [hsm, Matrix.det_smul, Fintype.card_fin]

  have hei : ∀ i : Fin n, (k : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Λ.Ln := fun i =>
    ⟨hkstd (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_std i)),
      Submodule.smul_mem _ _ (single_std i)⟩
  have hdete : Matrix.det (Matrix.of fun i j => ((k : 𝓞 E) • (Pi.single j 1 : Fin n → E)) i) = (k : E) ^ n := by
    rw [hdetk, det_single, _root_.mul_one]
  have hLa : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.La τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, fun i => (hei i).1, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hu : ∀ i, (k : 𝓞 E) • v i ∈ stdLat E n := fun i =>
        hkLa (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hv i))
      obtain ⟨r, hr⟩ := det_std hu
      rw [hdetk] at hr
      have h := hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
      rw [hr] at h
      simp only [map_mul, map_pow, hkv, one_pow, _root_.one_mul] at h
      exact h
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hLn : ∀ τ : E →+* ℂ, HasMax w (idealAt c Λ.Ln τ) 1 := fun τ => by
    refine hasMax_span hw ?_ ⟨_, ⟨_, ⟨_, hei, rfl⟩, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact (hLa τ).1 _ (Submodule.subset_span ⟨_, ⟨v, fun i => (hv i).1, rfl⟩, rfl⟩)
    · rw [hdete]; simp only [map_pow, hkv, one_pow]
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hLn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (hLa τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyw⟩ := e1.2
  have := e2.1 y (hs hy)
  simpa [hyw] using this

end GlobalTheory.LatticeIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectedLatticeDetIdealTypeNormIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  intro E _ _ _ H Dw l c n Λ N M ℓ hL hl A s hs T io hu e
  have hN : N ≠ 0 := by rintro rfl; exact absurd hL.1 (by decide)
  let w := (valV (K' := T.Fr) T.V).comap io
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => valV_integral T
    (by convert map_isIntegral_int io hx; exact Subsingleton.elim _ _)
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => hwi _ r.isIntegral_coe
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
  have hnat : ∀ τ (k : ℕ), Nat.Coprime k ℓ → w.comap (embF c τ) (k : E) = 1 := fun τ k hk => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valV_nat T hk hu
  have hn : ∀ τ, HasMax w (idealAt c Λ.Ln τ) (w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det)) := fun τ => by
    obtain ⟨a, b⟩ := detSet_Ln A _ (hwτ τ) (hnat τ _ A.cop₁)
    refine hasMax_span hw ?_ ⟨_, ⟨_, b, rfl⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have ha : ∀ τ, HasMax w (idealAt c Λ.La τ) (w.comap (embF c τ) A.ga.det)⁻¹ := fun τ => by
    obtain ⟨-, a, y, hy, b⟩ := detSet_La A _ (hwτ τ) (hnat τ _ A.cop)
    refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have h0 : ∀ τ, w.comap (embF c τ) A.ga.det ≠ 0 := fun τ => (detSet_La A _ (hwτ τ) (hnat τ _ A.cop)).1
  have hp : ∀ τ, w (embK c τ A.p.det) * (w.comap (embF c τ) A.ga.det)⁻¹ =
      w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det) := fun τ => by
    have := congrArg (w.comap (embF c τ)) (det_p A hN)
    simp only [map_mul, map_pow, hnat τ _ A.cop, hnat τ _ A.cop₁, _root_.one_pow, _root_.mul_one, _root_.one_mul] at this
    rw [mul_inv_eq_iff_eq_mul₀ (h0 τ), mul_comm]
    exact this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (ha τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyv⟩ := e1.2
  have hle := e2.1 y (hs hy)
  rw [hyv] at hle
  simp only [← hp, mul_pow, Finset.prod_mul_distrib, ← _root_.mul_assoc] at hle
  have hpos : 0 < ∏ τ : E →+* ℂ, (w.comap (embF c τ) A.ga.det)⁻¹ ^ Dw.mult τ :=
    zero_lt_iff.2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (inv_ne_zero (h0 τ)))
  have hw1 : w (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≤ 1 := by
    rw [map_mul, map_prod]
    simp only [map_pow]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [_root_.one_mul]
    exact hle
  have hv : valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) ≤ 1 := hw1
  by_cases hx : io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = 0
  · rw [hx, nval_zero]; exact le_top
  rw [nval_of_ne hx]
  have hlog : WithZero.log (valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log (valV_ne_zero hx) one_ne_zero).2 hv
  have h0v : (0 : ℝ) ≤ (vV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) : ℝ) := by
    simp only [vV]; exact_mod_cast (by omega)
  exact EReal.coe_nonneg.2 (div_nonneg h0v (Nat.cast_nonneg _))

end GlobalTheory.LatticeIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotientProdIrrUc
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GenSph

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
abbrev uc (a : ℂˣ) : IrrGL (k := k) := IrrGL.ofChar (unrChar k a) (isSmoothChar_of_isUnram (isUnram_unrChar k a))

theorem eq_first_of_isLSeg {Δ : Segment k} {y : IrrGL (k := k)} (h : IsLSeg Δ y.rep) (h1 : Δ.len = 1) : y = Δ.first := by
  have h2 := h.hasSupport
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3] at h2
  exact GlobalTheory.CompanionTheory.CuspPairSub.eq_of_hasSupport_singleton h2

theorem isSpherical_prodIrr_uc {c N : ℕ} (β : Fin c → ℂˣ) (hd : ∑ i, (uc k (β i)).1 = N) :
    IsSpherical (prodIrr (fun i => uc k (β i)) hd) := by
  have hv : ∀ i, ∃ v : (uc k (β i)).2.rep.V, v ≠ 0 ∧
      ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (uc k (β i)).1), (uc k (β i)).rep g v = v := fun i => by
    let r := IrrRep.det (Fin 1) (unrChar k (β i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (β i)))
    let e := equivRep r
    let u : r.V := (1 : ℂ)
    have hu : u ≠ 0 := show (1 : ℂ) ≠ 0 from one_ne_zero
    refine ⟨e u, fun h0 => hu (e.toLinearEquiv.injective (h0.trans (map_zero _).symm)), fun g hg => ?_⟩
    change GL (Fin 1) k at g
    have h1 := e.toIntertwiningMap.isIntertwining _ _ g u
    refine h1.symm.trans (congrArg e ?_)
    have h4 : unrChar k (β i) (Matrix.GeneralLinearGroup.det g) = 1 :=
      isUnram_unrChar k (β i) _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg)
    show ((ofChar (detChar (Fin 1) (unrChar k (β i)))) g) (1 : ℂ) = (1 : ℂ)
    simp [detChar_apply, h4]
  choose v hv0 hvK using hv
  obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (stdBlocks (fun i => (uc k (β i)).1) hd)
    (ρ := piTensor fun i => (uc k (β i)).rep) (x := PiTensorProduct.tprod ℂ v) fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext a
      exact hvK a _ (hg a)
  refine (Submodule.ne_bot_iff _).2 ⟨f, hf, fun h0 => ?_⟩
  have h5 : PiTensorProduct.tprod ℂ v = 0 := by rw [← hf1, h0]; rfl
  have hl : ∀ i, ∃ l : Module.Dual ℂ (uc k (β i)).2.rep.V, l (v i) ≠ 0 := fun i => by
    by_contra! hn
    exact hv0 i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hn)
  choose l hl using hl
  let ev : (⨂[ℂ] i, (uc k (β i)).2.rep.V) →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compLinearMap l)
  have h6 : ev (PiTensorProduct.tprod ℂ v) = ∏ i, l i (v i) := by simp [ev]
  rw [h5, map_zero] at h6
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hl i) h6.symm

theorem isSubquotient_prodIrr_uc {N : ℕ} (α : Fin N → ℂˣ) (hd : ∑ i, (uc k (α i)).1 = N) :
    IsSubquotient (prodIrr (fun i => uc k (α i)) hd) (prinSeries fun i => unrChar k (α i)) := by
  let φ := multiProdEquiv (stdBlocks (fun i => (uc k (α i)).1) hd) fun a =>
    (equivRep (IrrRep.det (Fin 1) (unrChar k (α a)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α a))))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ _)

end GlobalTheory.GenSph

namespace GlobalTheory.GenSph
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

end GlobalTheory.GenSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaTransformTheta

theorem isThetaFunO_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco φ hφ
  exact
    { quasi := fun γ w => _root_.GlobalTheory.ThetaQuasiRat.thetaTr_ratW_add D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ γ w
      level := _root_.GlobalTheory.ThetaLevel.thetaTr_level D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      cont := _root_.GlobalTheory.ThetaTrCont.continuous_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      smooth := fun k L hL hfin w => _root_.GlobalTheory.ThetaSmooth.contDiff_thetaTr_real D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ k L hL hfin w }

end GlobalTheory.ThetaTransformTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.XiSplit

open Formalism.L2.Host

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) : χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem smul_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.IndefR.Lev.IsConjPl w w') :
    D.host.conj • w.asIdeal = w'.asIdeal := by
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (GlobalTheory.TypePlaces.star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact hmax.eq_of_le w'.isPrime.ne_top hle

theorem isConjPl_of_smul_eq {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : D.host.conj • w.asIdeal = w'.asIdeal) : Formalism.IndefR.Lev.IsConjPl w w' := fun c hc =>
  ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩

theorem unrAt_of_inert {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    (L.xiH t).UnrAt P := by
  obtain ⟨q, -, hI, hqP⟩ := hP
  have hfix : D.host.conj • P.asIdeal = P.asIdeal := hI P.asIdeal P.isPrime P.ne_bot hqP
  by_contra h
  rcases (hL.Q_ram t P).1 h with hPQ | ⟨P', hP', hc⟩
  · exact ((hL.Q_pl t) P hPQ).2 P hPQ (isConjPl_of_smul_eq hfix)
  · have e1 := (smul_eq_of_isConjPl hc).trans hfix.symm
    have e2 : P'.asIdeal = P.asIdeal := by
      simpa using congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e1
    have e3 : P' = P := HeightOneSpectrum.ext e2
    subst e3
    exact ((hL.Q_pl t) P' hP').2 P' hP' hc

theorem exists_heckeU_xi : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    ∃ χ : HeckeU D 0, (∀ x, χ.f x = (L.xiH t).1 (finIdl D x)) ∧ ∀ τ, χ.n τ = 0 := by
  intro D T L μ₀ hL t
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hu : (L.xiH t).IsUnitary := isUnitary_of_orderDvd hn ho
  have hi : (L.xiH t).HasInf (Formalism.L2.Host.embTau D) 0 := fun k => by
    rw [inf_eq_one hn ho k]
    simp
  have hp : ∀ τ, Even ((0 : D.what₂.Tau → ℤ) τ - ((0 : ℕ) : ℤ)) := fun τ => by simp
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (L.xiH t).1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t)
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  have hnorm := GlobalTheory.NuCharNorm.chi_norm_one D (L.xiH t) (hL.xi_triv t)
    (GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t))
  have hr := GlobalTheory.UnrKill.unr_kill D (L.xiH t) (unrAt_of_inert hL t)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar 0 (L.xiH t) 0 hu hi hp hc hnorm hr, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.XiSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThird
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

attribute [local instance high] Submodule.module

theorem mumaxTop : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := fun hT =>
  GlobalTheory.LamMuMax.slopeMax_le (_root_.GlobalTheory.UCls.massBound_of_tamagawa hT)
    _root_.GlobalTheory.UCls.torusBound

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperator
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
end
end

