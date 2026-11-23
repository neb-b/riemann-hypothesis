module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem absA_pos (z : (AE D)ˣ) : 0 < absA D z := by
  have h : absA D z * absA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem npow_neg_nat {r : ℝ≥0} (hr : 0 < r) (m : ℕ) : ((((r ^ m)⁻¹ : ℝ≥0) : ℝ) : ℂ) = npow r (-(m : ℂ)) := by
  have h0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem integral_comp_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (f : A → ℂ) :
    ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ y, f (φ y) ∂μ :=
    integral_map_equiv (μ := μ) φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (x y : hermA D n) : nb (x + y) = nb x * nb y :=
  mat_inj (by
    rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
    simp [add_comm])

def cg (a : GL (Fin n) (AE D)) (c : hermA D n) : hermA D n :=
  ⟨a.1 * c.1 * adj a.1, by
    change adj (a.1 * c.1 * adj a.1) = a.1 * c.1 * adj a.1
    have hc : adj c.1 = c.1 := c.2
    rw [adj_mul, adj_mul, adj_adj, hc, Matrix.mul_assoc]⟩

theorem adj_mul_adj_inv (a : GL (Fin n) (AE D)) : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_inv_mul_adj (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

def ad (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1, adj_inv_mul_adj a, adj_mul_adj_inv a⟩

theorem nb_cg_mul {nb : hermA D n → G D n} (h : IsNMap nb) (a : GL (Fin n) (AE D)) {m : G D n}
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (c : hermA D n) : nb (cg a c) * m = m * nb c :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, h, h, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    have e : a.1 * c.1 * adj a.1 * adj (a⁻¹).1 = a.1 * c.1 := by
      rw [Matrix.mul_assoc, adj_mul_adj_inv, Matrix.mul_one]
    simp [cg, e, -Matrix.coe_units_inv])

theorem weyl_mul {w m m' : G D n} (hw : mat w = blk4 0 1 (-1) 0) (a : GL (Fin n) (AE D))
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (hm' : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1) : w * m = m' * w :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, hw, hm', submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp)

theorem mulVec_mem_upper {g : G D n} {x y : Mx D n n} (hg : mat g = blk4 x 0 0 y) {v : Fin (n + n) → AE D}
    (hv : v ∈ upperHalf D n) : (mat g).mulVec v ∈ upperHalf D n := by
  have hv' : ∀ i : Fin n, v (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := fun i => congrFun hv i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  simp only [LinearMap.funLeft_apply, Pi.zero_apply, hg, Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    hv', mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem levi_mem_P {g g' : G D n} {x y x' y' : Mx D n n} (hg : mat g = blk4 x 0 0 y) (hg' : mat g' = blk4 x' 0 0 y')
    (h1 : g' * g = 1) : g ∈ P D n := by
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_left h1
  intro v
  refine ⟨fun hv => mulVec_mem_upper hg hv, fun hv => ?_⟩
  have h2 := mulVec_mem_upper hg' (v := (mat g).mulVec v) hv
  rwa [Matrix.mulVec_mulVec, ← mat_mul, h1, mat_one, Matrix.one_mulVec] at h2

theorem height_mul {H : G D n → ℝ≥0} (hH : IsHeight H) {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) (x : G D n) :
    H (p * x) = absA D (Matrix.GeneralLinearGroup.det a) * H x := by
  obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨c, hc⟩ := exists_blkA hq
  have e : blkA (mat (p * q)) = (a * c).1 := by rw [blkA_mul hq, ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hq) (a * c) e k hk, hH q hq c hc k hk, map_mul, map_mul]

end GlobalTheory.CompanionTheory.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSocleProdIrrCongr
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isSocle_prodIrr_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL (k := k)} (e : y = z)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) (H : IsSocle π (prodIrr y hy)) :
    IsSocle π (prodIrr z hz) := by
  subst e
  exact H

theorem socleOne : PositivityTheory.SphericalProduct.SocleOne := by
  intro k _ _ _ _ _ n ξ hξ hanti hd
  let x : Fin n → IrrGL (k := k) := fun i =>
    IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))
  have hLF : LFactors (PositivityTheory.SphericalProduct.msOne ξ hξ) x :=
    ⟨_, GlobalTheory.CompanionTheory.OneTermOrder.isOrderedForm_single_rev k n ξ hξ hanti, fun i => isLSeg_single k _ _⟩
  have hd1 : ∑ a, (x a).1 = n := by simp [x, IrrGL.ofChar]
  have hd2 : ∑ a, (x (Fin.rev a)).1 = n := by simp [x, IrrGL.ofChar]
  refine ⟨?_, ?_⟩
  · obtain ⟨π, hπ⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hd1 hLF
    have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π.ρ := ⟨n, x, hd1, hLF, hπ⟩
    exact ⟨IrrGL.of π.ρ π.smooth π.irr, rfl, hL.of_equiv (IrrGL.equivOf _ _ _)⟩
  · intro V _ _ π hL
    have hS := PositivityTheory.Exh.lSocleGL_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ n n x hd2 hLF π hL
    refine isSocle_prodIrr_congr ?_ _ hd hS
    funext a
    simp only [x, Function.comp, Fin.rev_rev]

end GlobalTheory.CompanionTheory.LocGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuLocal

open Formalism.L2.Host GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnitAt_of_valuation (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (h : ValuativeRel.valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1) : IsUnitAt w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 := GlobalTheory.SmGL.ord_eq_zero_iff.2 h
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at h1
  rw [IsUnitAt, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem loc_eq_unrChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) :
    χ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ.val w) :=
  GlobalTheory.PrinSat.eq_unrChar_of_ord (fun x hx => h x (isUnitAt_of_valuation w x hx)) (GlobalTheory.PrinSat.ord_unif w)

theorem loc_pow (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (x : (w.adicCompletion E)ˣ) :
    (χ ^ k).loc w x = χ.loc w x ^ k := by
  simp [HChar.loc]

theorem loc_mul_loc_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : GlobalTheory.BCT.IsMu μ e) (w : HeightOneSpectrum (𝓞 E))
    (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ) :
    μ.loc (GlobalTheory.ThetaSatake.cw w) x * μ.loc w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) = 1 := by
  have h1 := GlobalTheory.BCT.MuProps.mu_mul_conj h (Neutral.B1.localIdele E _ x)
  rw [GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.ThetaPull.conjAd_localIdele] at h1
  exact h1

theorem isUnitAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnitAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnitAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

theorem isUnifAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnifAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnifAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

end GlobalTheory.CompanionTheory.MuLocal


open GlobalTheory.CompanionTheory.MuLocal Formalism.L2.Host GlobalTheory.CuspRep in
theorem GlobalTheory.CompanionTheory.MuLocal.muLoc_holds : PositivityTheory.Rg.BcB.F.RS.MuLoc := by
  intro E _ _ _ _ μ e w hμ hun
  refine ⟨loc_eq_unrChar hun, fun k => ⟨fun x hx => ?_, ?_⟩, fun u _ hu => ?_⟩
  · rw [loc_pow, hun x hx, one_pow]
  · rw [HChar.val, HChar.locK, MonoidHom.comp_apply, loc_pow]
    rfl
  · obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hu
    have hc := loc_mul_loc_conj hμ w
    refine ⟨fun x hx => ?_, ?_⟩
    · have h2 := hc x
      rw [hun _ (isUnitAt_conj w x hx), mul_one] at h2
      exact h2
    · have h2 := hc (atFin (GlobalTheory.ThetaSatake.cw w) (unif (GlobalTheory.ThetaSatake.cw w)))
      rw [μ.val_eq hun _ (isUnifAt_conj w _ (unif_spec _))] at h2
      exact eq_inv_of_mul_eq_one_left h2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBound
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.OneSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_unifU : valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  have hϖ := Zls.irreducible_unif (k := k)
  apply le_antisymm
  · exact le_uniformizer_iff.2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hϖ.not_isUnit)
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hlt : valuation k y < 1 := hy ▸ uniformizer_lt_one
    rw [← hy]
    exact (mem_cball_uniformiser hϖ (x := Zls.unifU k) rfl ⟨y, hlt.le⟩).2
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hlt)

theorem hasSatake_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} {α : Fin n → ℂˣ}
    (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_, ?_⟩
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
    refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective ?_)⟩
    · have h1 := hv g
      have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
      rw [← e, h1, map_smul]
    · simpa using e
  · exact (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2

theorem isUnramChar_of_isCusp_of_isSpherical [CharZero k] (x : IrrGL (k := k)) (hx : x.IsCusp) (hs : IsSpherical x.rep) :
    x.IsUnramChar := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := _root_.GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma hBZ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

theorem len_eq_one [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)) (hL : IsLSeg Δ y.rep) (hS : IsSpherical y.rep) :
    Δ.len = 1 := by
  have hLM := PositivityTheory.Exh.langlandsMultisegments_holds
  have hSC := PositivityTheory.Exh.standardCosocleGL_holds
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL (k := k), x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    isUnramChar_of_isCusp_of_isSpherical Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN
  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'
  have hϖ := valuation_unifU (k := k)
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) (Zls.unifU k)
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := _root_.GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (_root_.GlobalTheory.LocGL.isL_det hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

theorem isL_single_unrChar [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ) (hsat : HasSatake x.rep α) :
    IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  obtain ⟨𝔪, hL⟩ := PositivityTheory.Exh.langlandsExhaustionGL_holds k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL
  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1
  have hlen : ∀ i, (Δ i).len = 1 := fun i => len_eq_one (Δ i) (y i) (hseg i) (hsphy i)
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)
  have h1 : HasSupport x.rep (∑ a, (Δ a).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun a => (hseg a).hasSupport) x.2.rep.irr
      hcos.isSubquotient
  have h2 := _root_.GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries k x.1 (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h1 h2
  have hsupp : (∑ a, (Δ a).ms) = Finset.univ.val.map fun i => (Δ i).first := by
    simp only [hms]
    rw [Finset.sum_eq_multiset_sum]
    exact Multiset.bind_singleton Finset.univ.val fun i => (Δ i).first
  rw [hsupp] at heq
  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.CompanionTheory.OneSat


open GlobalTheory.CompanionTheory.OneSat in
theorem GlobalTheory.CompanionTheory.OneSat.lOneSat : PositivityTheory.SphericalProduct.LOneSat := by
  intro k _ _ _ _ _ n ξ hξ V _ _ π hs
  have hϖ := valuation_unifU (k := k)
  have hms : ∀ (χ χ' : kˣ →* ℂˣ) (h : IsSmoothChar χ) (h' : IsSmoothChar χ') (c) (c'), χ = χ' →
      Segment.single (IrrGL.ofChar χ h) c = Segment.single (IrrGL.ofChar χ' h') c' := by
    rintro χ _ h h' c c' rfl; rfl
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth τ →
      HasSatake τ (PositivityTheory.SphericalProduct.atUnif k ξ) → IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) τ := by
    intro W _ _ τ hτ hsat
    have φ := IrrGL.equivOf τ hτ hsat.1
    have h1 := isL_single_unrChar (IrrGL.of τ hτ hsat.1) (PositivityTheory.SphericalProduct.atUnif k ξ) (hasSatake_of_equiv φ hsat)
    have h2 : PositivityTheory.SphericalProduct.msOne ξ hξ = Finset.univ.val.map fun i : Fin n =>
        Segment.single (IrrGL.ofChar (unrChar k (PositivityTheory.SphericalProduct.atUnif k ξ i))
          (isSmoothChar_of_isUnram (isUnram_unrChar k _))) (IrrGL.isCusp_ofChar _ _) :=
      Multiset.map_congr rfl fun i _ => hms _ _ _ _ _ _ (eq_unrChar (hξ i) hϖ)
    rw [h2]
    exact h1.of_equiv φ.symm
  refine ⟨fun hL => ?_, key π hs⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) (PositivityTheory.SphericalProduct.atUnif k ξ)
  have hLy := key y.ρ y.smooth hy
  obtain ⟨h, x, hd, hx, hc⟩ := hL
  have hc' := PositivityTheory.Exh.lOrderFree_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ h n x hd hx y.ρ hLy
  obtain ⟨e⟩ := hc.unique hc'
  exact hasSatake_of_equiv e hy

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecomp
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.LeviCf

theorem entries_of_unip_lev {R : Type} [CommRing R] {r s : ℕ} (S : Set R) (x : BlockIx (r + s) r → R)
    (g : GL (Fin r) R × GL (Fin s) R)
    (h : ∀ a b : Fin (r + s), ((unip x * lev R r s g : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S)
    (h' : ∀ a b : Fin (r + s),
      (((unip x * lev R r s g)⁻¹ : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S) :
    ((∀ a b : Fin r, (g.1 : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
        ∀ a b : Fin r, ((g.1⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
      ((∀ a b : Fin s, (g.2 : Matrix (Fin s) (Fin s) R) a b ∈ S) ∧
        ∀ a b : Fin s, ((g.2⁻¹ : GL (Fin s) R) : Matrix (Fin s) (Fin s) R) a b ∈ S) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (g⁻¹) (-x)
  have hu : (unip x : GL (Fin (r + s)) R)⁻¹ = unip (-x) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have hi : (unip x * lev R r s g : GL (Fin (r + s)) R)⁻¹ = unip v * lev R r s g⁻¹ := by
    rw [_root_.mul_inv_rev, hu, ← map_inv, hv]
  rw [hi] at h'
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, fun a b => ?_, fun a b => ?_⟩
  · rw [← unip_lev_cc x g a b]; exact h _ _
  · have := unip_lev_cc v g⁻¹ a b
    rw [Prod.fst_inv] at this
    rw [← this]; exact h' _ _
  · rw [← unip_lev_nn x g a b]; exact h _ _
  · have := unip_lev_nn v g⁻¹ a b
    rw [Prod.snd_inv] at this
    rw [← this]; exact h' _ _

theorem levi_cf_integral {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E))
    (hc : c ∈ KO E (r + s)) (h : unip u * lev (Ad E) r s m = cf (r + s) k c) :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf h
  have f1 : GeneralLinearGroup.map (pFin E) m.1 = g₁ := by
    rw [hm, cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have f2 : GeneralLinearGroup.map (pFin E) m.2 = g₂ := by
    rw [show m.2 = cf s k₂ g₂ by rw [hm], cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h2 := congrArg (GeneralLinearGroup.map (pFin E)) h
  rw [map_mul, IwaAd.map_unip, IwaAd.map_lev, cf, map_mul, pFin_infGL, pFin_finGL, one_mul, f1, f2] at h2
  obtain ⟨hc1, hc2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E (r + s)).1 hc
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := entries_of_unip_lev (↑(GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : Set (Af E)) _ (g₁, g₂)
    (by rw [h2]; exact hc1) (by rw [h2]; exact hc2)
  exact ⟨k₁, g₁, k₂, g₂, (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E r).2 ⟨a1, a2⟩,
    (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E s).2 ⟨b1, b2⟩, hm⟩

end GlobalTheory.CompanionTheory.LimV.LeviCf

end
end

