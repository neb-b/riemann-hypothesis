module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.RowTest.CosetFin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem finDatum_eq {t : T} {p : Pair T} {k : ℕ} {a b : FinDatum G t p} (ha : IsCosetDatum k a) (hb : IsCosetDatum k b)
    (hP : a.P = b.P) (he : a.e = b.e) (hz : a.z = b.z) {u} (hu : a.fn u ≠ 0) (hu' : b.fn u ≠ 0) : a = b := by
  have hf := ha.fn_eq hb he hu hu'
  cases a
  cases b
  simp only at hP he hz hf
  subst hP he hz hf
  rfl

theorem pureDat_eq {t : T} {k : ℕ} {e : AE D} {d d' : PureDat G t}
    (hc : (∀ j, IsCosetDatum k (d.1 j)) ∧ ∀ i, IsCosetDatum k (d.2 i))
    (hc' : (∀ j, IsCosetDatum k (d'.1 j)) ∧ ∀ i, IsCosetDatum k (d'.2 i))
    (hp : (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hp' : (∀ j, (d'.1 j).P = locPl G t ∧ (d'.1 j).e = e ∧ (d'.1 j).z = 1) ∧
      ∀ i, (d'.2 i).P = locPl G t ∧ (d'.2 i).e = e ∧ (d'.2 i).z = 1)
    (hx : ∀ j, ∃ u, (d.1 j).fn u ≠ 0 ∧ (d'.1 j).fn u ≠ 0) (hy : ∀ i, ∃ u, (d.2 i).fn u ≠ 0 ∧ (d'.2 i).fn u ≠ 0) : d = d' := by
  refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
  · obtain ⟨a1, a2, a3⟩ := hp.1 j
    obtain ⟨b1, b2, b3⟩ := hp'.1 j
    obtain ⟨u, hu, hu'⟩ := hx j
    exact finDatum_eq (hc.1 j) (hc'.1 j) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'
  · obtain ⟨a1, a2, a3⟩ := hp.2 i
    obtain ⟨b1, b2, b3⟩ := hp'.2 i
    obtain ⟨u, hu, hu'⟩ := hy i
    exact finDatum_eq (hc.2 i) (hc'.2 i) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'

end GlobalTheory.RowTest.CosetFin

namespace GlobalTheory.RowTest.CosetFin

section Sums

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t}

theorem mem_support_of {k : ℕ} {τ₀ τ : PureDat G t →₀ ℂ} (h₀ : IsCosetExpansion S t Φ β k τ₀)
    (h : IsCosetExpansion S t Φ β k τ) {d : PureDat G t} (hd : d ∈ τ.support) : d ∈ τ₀.support := by
  obtain ⟨-, ⟨e, he, h1, h2⟩, h3⟩ := h
  obtain ⟨-, ⟨e₀, he₀, h1₀, h2₀⟩, h3₀⟩ := h₀
  have hee : e₀ = e := GlobalTheory.StepVecSum.idemSum_eq (G.V (.top 0)) he he₀
  subst hee
  choose x hx _ hx' using (h3 d hd).1
  choose y hy _ hy' using (h3 d hd).2
  have ex : ∀ j, (d.1 j).fn (x j) = 1 := fun j => by rw [hx', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have ey : ∀ i, (d.2 i).fn (y i) = 1 := fun i => by rw [hy', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have hs : (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = τ d := by
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem d hd]
    · simp [ex, ey]
    · intro d' hd' hne
      by_contra h0
      obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
      exact hne (pureDat_eq (h3 d' hd') (h3 d hd) (h1 d' hd') (h1 d hd)
        (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
        (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩))
  have hxe := fun j => ((h1 d hd).1 j).2.1 ▸ hx j
  have hye := fun i => ((h1 d hd).2 i).2.1 ▸ hy i
  have hne : (τ₀.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) ≠ 0 := by
    rw [h2₀ x y hxe hye, ← h2 x y hxe hye, hs]
    exact Finsupp.mem_support_iff.1 hd
  obtain ⟨d', hd', h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
  have hdd : d' = d := pureDat_eq (h3₀ d' hd') (h3 d hd) (h1₀ d' hd') (h1 d hd)
    (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
    (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩)
  exact hdd ▸ hd'

end Sums

theorem finite_pureDat_of_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  intro D T L sc G W U S t Φ β k
  by_cases h : ∃ τ₀, IsCosetExpansion S t Φ β k τ₀
  · obtain ⟨τ₀, h₀⟩ := h
    exact τ₀.support.finite_toSet.subset fun d ⟨τ, hτ, hd⟩ => mem_support_of h₀ hτ hd
  · refine Set.finite_empty.subset ?_
    rintro d ⟨τ, hτ, -⟩
    exact h ⟨τ, hτ⟩

end GlobalTheory.RowTest.CosetFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedean
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GfCArch

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun a := ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((a + b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((c • a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_fst (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : u • x = 0 := by
  let e : AF F := ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  let f : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F f = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h0 : f • u = 0 := hu f hf
  have hef : e + f = 1 := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) + 0 = 1
      rw [add_zero]
    · show (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + 1 = 1
      rw [zero_add]
  have hu' : u = e * u := by
    calc u = (e + f) * u := by rw [hef, one_mul]
      _ = e * u + f • u := add_mul _ _ _
      _ = e * u := by rw [h0, add_zero]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (infIncl F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        (((show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact one_mul _
      · exact zero_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_comm, mul_smul, key, hx, map_zero, smul_zero]

theorem gfc_arch : ∀ (D : D7) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X), g ∈ GfC X →
    ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1) = 0 := by
  intro D X k e J hJ g hg u hu
  have hM : ∀ a b, Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 :=
    (GlobalTheory.FinPl.KOpen.mem_GfC_iff X g).1 hg
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_fst _ _ _ (hM _ _) u hu

end GlobalTheory.GfCArch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem hasSum_of_eq {ι M : Type} [NormedAddCommGroup M] {f g : ι → M} {a b : M} (h : HasSum f a) (hf : ∀ i, g i = f i)
    (ha : b = a) : HasSum g b := by
  rwa [funext hf, ha]

theorem l2_smul_left {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (c : ℂ) (f g : X → ℂ) :
    l2 μ 𝓕 (c • f) g = c * l2 μ 𝓕 f g := by
  simp only [l2, Formalism.IndefR.Lift.pet, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem l2_self_eq_setIntegral_norm_sq {a b : ℕ} (μ : Measure (Mx D a b)) (𝓕 : Set (Mx D a b)) (f : Mx D a b → ℂ) :
    l2 μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  simp only [l2, Formalism.IndefR.Lift.pet, nrm2, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]

theorem mult_values (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ)
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (x : M.Vec) :
    U x ∈ bddAut V ∧ ∀ k ∈ J, ∀ g, U x (g * k) = χ k * U x g := by
  induction hU using Submodule.span_induction with
  | mem U h => exact ⟨⟨(h.aut x).cont, (h.aut x).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h.aut x) (h.cusp x)⟩, h.lev x⟩
  | zero => exact ⟨zero_mem _, fun _ _ _ => by simp⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, fun k hk g => by simp [ha.2 k hk, hb.2 k hk, mul_add]⟩
  | smul c a _ ha => exact ⟨(bddAut V).smul_mem c ha.1, fun k hk g => by simp [ha.2 k hk, mul_left_comm]⟩

theorem part_eigen {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ} {U : MMap M}
    (hU : U ∈ partFull θ M J χ Sb c) (x : M.Vec) (w d R) (h : Hecke₂ V J χ Sb w d R) :
    heckeLin V R (U x) = c w d • U x := by
  have h1 := hU.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
  exact congrArg (fun T : MMap M => T x) (h1 w d R h)

theorem isParamVec_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : IsParamVec σ J L h ρ' (f x) B) : IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

def satur (V : HSp D) (J : Subgroup (GA D V)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GA D V) where
  carrier := {g | g ∈ GfC V ∧ ∃ k ∈ J, ∀ v ∈ S, projV V v g = projV V v k}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, k, hk, h⟩ ⟨hb, k', hk', h'⟩
    exact ⟨mul_mem ha hb, k * k', mul_mem hk hk', fun v hv => by rw [map_mul, map_mul, h v hv, h' v hv]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, h⟩
    exact ⟨inv_mem ha, k⁻¹, inv_mem hk, fun v hv => by rw [map_inv, map_inv, h v hv]⟩


set_option maxHeartbeats 1000000 in
theorem zeta_sum (hG : GlobalTheory.Published.UnramifiedDoublingGL) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (rS : S.rank = D.R.nV)
    (rT : T.rank = D.R.r) {μ : Measure (WO S T)} {𝓧 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓧)
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hu : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → UnrAt χS w ∧ UnrAt χT w)
    {K J : Subgroup (GA D T)} {χ : GA D T → ℂ} (hKJ : K ≤ J) (hidx : K.relIndex J ≠ 0) (hJf : J ≤ GfC T)
    (hJ : ∀ g ∈ GfC T, g ∈ J ↔ (∃ k ∈ J, ∀ v ∈ Sb, projV T v g = projV T v k) ∧ ∀ v ∉ Sb, projV T v g ∈ Kv T v)
    (hfin : ∀ g : GA D T, {v | projV T v g ∉ Kv T v}.Finite) (hχ : ∀ k ∈ J, ‖χ k‖ = 1)
    {f : WO S T → ℂ} (hvac : ∀ v ∉ Sb, VacFin ψ S T v f) (hlaw : ∀ k ∈ J, om (1, k) f = χ k • f)
    (hvan : ∀ g ∈ GfC T, g ∉ satur T J Sb → l2 μ 𝓧 (om (1, g) f) f = 0)
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν)
    (F₁ F₂ : bddAut T) (hlev : ∀ k ∈ J, ∀ g, F₁.1 (g * k) = χ k * F₁.1 g) {B : Fam D.host.E} (hB : IsParamFunV T Sb F₁.1 B)
    (hb : Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2))
    (hc : Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χS)⁻¹) ((1 + (D.R.t : ℂ)) / 2)) :
    HasSum (fun y : FinCos T K => l2 μ 𝓧 (om (1, y.rep) f) f * starRingEnd ℂ (l2 ν 𝓕 (rTr T y.rep F₁) F₂))
      ((K.relIndex J : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (LSD D Sb B χS ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) *
        starRingEnd ℂ (l2 ν 𝓕 F₁ F₂)) := by
  obtain ⟨hun, hℓ⟩ := _root_.GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D T
  obtain ⟨ℓ, hℓ, hbd⟩ := hℓ ν 𝓕 hν h𝓕 F₂
  obtain ⟨C, hC⟩ := hbd F₁
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  choose φ hφ hφ' using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
    _root_.GlobalTheory.VacCoef.vac_coef D ψ S T χS χT om hW μ 𝓧 hμ v.1 fun w h => hu w (h ▸ v.2)
  rw [rS] at hφ
  obtain ⟨A, hA, hA'⟩ := _root_.GlobalTheory.FinZeta.AbsConv.absConv_localZeta hG D T rT (val χS) (norm_val χS) Sb φ hφ
  let co : GA D T → ℂ := fun g => l2 μ 𝓧 (om (1, g) f) f
  let Ψ : GA D T → ℂ := fun g => co g * starRingEnd ℂ (ℓ (bddRep T g F₁))
  have hmul : ∀ g k : GA D T, om (1, g * k) f = om (1, g) (om (1, k) f) := fun g k => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have co1 : ∀ g, ∀ k ∈ J, co (g * k) = χ k * co g := fun g k hk => by
    simp only [co, hmul, hlaw k hk, map_smul, l2_smul_left]
  have F1 : ∀ k ∈ J, bddRep T k F₁ = χ k • F₁ := fun k hk => Subtype.ext (funext fun g => hlev k hk g)
  have Ψ1 : ∀ g, ∀ k ∈ J, Ψ (g * k) = Ψ g := fun g k hk => by
    have h1 : χ k * starRingEnd ℂ (χ k) = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ k hk]; simp
    simp only [Ψ, co1 g k hk, map_mul, Module.End.mul_apply, F1 k hk, map_smul, smul_eq_mul]
    linear_combination (co g * starRingEnd ℂ (ℓ (bddRep T g F₁))) * h1
  have co2 : ∀ (v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}) g, projV T v.1 g = 1 → ∀ a,
      co (g * embV T v.1 a) = φ v a * co g := fun v g hg a => by
    simp only [co]
    rw [← (commute_emb D.sp.cm.sig T.gram a hg).eq, hmul]
    exact hφ' v a _ _ (_root_.GlobalTheory.FinZeta.MoveVac.vacFin_om_one D ψ S T χS χT om hW v.1 g hg f (hvac v.1 v.2)) (hvac v.1 v.2)
  have hJH : J ≤ satur T J Sb := fun k hk => ⟨hJf hk, k, hk, fun _ _ => rfl⟩
  have key := _root_.GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => embV T v.1) (fun v => projV T v.1)
    (fun v => Kv T v.1) J (satur T J Sb) hJH (fun v a => proj_emb_self _ _ _ _)
    (fun u v h a => proj_emb_ne _ _ (fun e => h (Subtype.ext e)) a)
    (fun v a => ⟨mem_finPts.2 (projInf_emb _ _ _ _), 1, one_mem _, fun u hu' => by
      rw [map_one]; exact proj_emb_ne _ _ (fun e : u = v.1 => v.2 (e ▸ hu')) a⟩)
    (fun v a g hg => commute_emb _ _ a hg)
    (fun g hg => (hJ g hg.1).trans ⟨fun h v => h.2 v.1 v.2, fun h => ⟨hg.2, fun v hv => h ⟨v, hv⟩⟩⟩)
    (fun g _ => (hfin g).preimage Subtype.val_injective.injOn)
    Ψ (fun g => C * ‖co g‖) _ A _ (fun g _ => Ψ1 g) (fun g _ k hk => by rw [co1 g k hk, norm_mul, hχ k hk, one_mul])
    (fun g _ => by
      simp only [Ψ, norm_mul, RCLike.norm_conj]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hC g) (norm_nonneg _))
    (fun v g _ hg => by
      have h1 := _root_.GlobalTheory.LocZeta.hasSum_localZeta hG D T rT χS (rS ▸ hW.resS) v.1 (fun w h => (hu w (h ▸ v.2)).1) (φ v) (hφ v) _
        ((bddRep T).comp (embV T v.1)) (by
          obtain ⟨b, b1, b2, b3⟩ := hun
          exact ⟨b, b1, b2, fun g => b3 _⟩) F₁ B
        (fun w h => ⟨isParamVec_sub (bddAut T).subtype (fun _ _ => rfl) Subtype.val_injective (hB v.1 v.2 w h),
          (hb w (show w.under (𝓞 D.host.F) ∉ (Sb : Set _) from h ▸ v.2)).2⟩) (ℓ ∘ₗ bddRep T g)
        ⟨C, fun a => by
          have := hC (g * embV T v.1 a)
          rwa [map_mul] at this⟩
      refine hasSum_of_eq (h1.mul_left (co g)) (fun a => ?_) ?_
      · simp only [Ψ, co2 v g hg, map_mul, Module.End.mul_apply, LinearMap.comp_apply, MonoidHom.comp_apply]
        ring
      · simp only [Ψ, LinearMap.comp_apply]
        ring)
    (fun v g _ hg => by
      refine hasSum_of_eq ((hA' v).mul_right (C * ‖co g‖)) (fun a => ?_) rfl
      rw [co2 v g hg, norm_mul]
      ring)
    hA (_root_.GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc D Sb B χS hc)
  have fin := _root_.GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul K J (satur T J Sb) (GfC T) hKJ hJH (fun g hg => hg.1) hidx Ψ _
    (fun g hg hg' => by simp only [Ψ, co, hvan g hg hg', zero_mul]) (fun g _ => Ψ1 g) key
  refine hasSum_of_eq fin (fun y => ?_) ?_
  · simp only [Ψ, co, hℓ, coe_bddRep, FinCos.rep]
  · have : ((1, 1) : GA D S × GA D T) = 1 := rfl
    simp only [Ψ, co, this, map_one, Module.End.one_apply, l2_self_eq_setIntegral_norm_sq, hℓ]
    ring


set_option maxHeartbeats 1000000 in
theorem finiteZetaL : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
      [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  classical
  intro hP _ hG D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨hft, hvac⟩ := _root_.GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m ω BW f₀ f c io hd
  have hlaw := GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter R F i t σ s P cμ cη m ω BW f₀ f c io hd
  obtain ⟨hC, -, -, -, hch, hW, -, hf, -⟩ := hd
  obtain ⟨-, e, he, hΘ⟩ := isLevelVec_iff.1 hf
  have rV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨a, bV⟩ := hC.lev.βV i
  obtain ⟨b, bW⟩ := hC.lev.βW i
  rw [one_pow] at bV bW
  obtain ⟨hs, hJ, hfin, hχ⟩ := _root_.GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i P) (finS R t) bW fun PP h =>
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ (h.resolve_right (Finset.notMem_empty _)))
  obtain ⟨hKJ, hidx, hidx'⟩ := _root_.GlobalTheory.LevIdx.levidx D T R.toLevCh A.μ0 hC.lev _ e he Finset.subset_union_left i P
  have hu := (GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hC.lev i t s cμ cη m hch).2.2
  have hvan : ∀ g ∈ GfC (Wc D i), g ∉ satur (Wc D i) (levG _ (R.βW i) (R.datWp i P)) (finS R t) →
      l2 μ 𝓧 (ω (1, g) f) f = 0 := fun g hg hg' => by
    refine _root_.GlobalTheory.ThetaOrth.orth D _ _ _ _ _ ω hW _ _ sdV sdW _ e he f₀ _ f (_root_.GlobalTheory.FinZeta.isSBHalf_levDatum D _ _ _ _ _ _ _ _ _ _ e sdV sdW bV.1 bW.1 he) hΘ hft μ 𝓧 hμ g hg
      fun x hx => by_contra fun hx' => hg' ⟨hg, ?_⟩
    obtain ⟨k, hk, h⟩ := _root_.GlobalTheory.SuppLev.supp_level D _ _ _ _ _ _ _ _ _ e sdW bW.1 (by rw [rV, rW]; exact Nat.le_add_right _ _) rfl he
      (fun PP => Finset.mem_union) g hg x hx hx'
    refine ⟨k, hk, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    exact h PP hPP
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hU0 : (R.HW i σ).e x ≠ 0 := fun h => hx0 ((hC.models.HW i σ).1 (h.trans (map_zero _).symm))
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, (R.HW i σ).e x v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨m1, m2⟩ := mult_values hP hC.models.inf hx.1 v₀
  obtain ⟨B, hB, hb⟩ := _root_.GlobalTheory.FinZeta.ParamBound.exists_param_bounded D (Wc D i) _ _ (finS R t) hs _ m1 hv₀ m2 ev (part_eigen hx v₀)
  have hsys := (isParamFunV_iff_of_mem_partFull hs hx hv₀ B).1 hB
  rw [rW] at hb
  have hconv := hb.converges_twist_val cμ (s := (1 + (D.R.t : ℂ)) / 2) (by
    have h5 : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have : ((1 + (D.R.t : ℂ)) / 2).re = (1 + (D.R.t : ℝ)) / 2 := by
      rw [show (1 + (D.R.t : ℂ)) / 2 = (((1 + (D.R.t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    rw [this]
    linarith)
  refine ⟨B, rW ▸ hsys, fun w hw => (hb w (offS_iff.1 hw)).2, hconv, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  by_cases h0 : U₁ v₁ = 0
  · have : ∀ g, rTr (Wc D i) g 0 = 0 := fun _ => rfl
    simp only [h0, this, petW, l2, Formalism.IndefR.Lift.pet, Pi.zero_apply, zero_mul, integral_zero, map_zero, mul_zero]
    exact hasSum_zero
  obtain ⟨n1, n2⟩ := mult_values hP hC.models.inf h₁.1 v₁
  rw [← hidx]
  exact zeta_sum hG hW rV rW hμ hu hKJ (hidx ▸ hidx') (fun k hk => hk.1) hJ hfin hχ hvac hlaw hvan (hC.models.νW i).1.1
    (hC.models.νW i).2 ⟨_, n1⟩ ⟨_, (mult_values hP hC.models.inf h₂ v₂).1⟩ n2
    ((isParamFunV_iff_of_mem_partFull hs h₁ h0 B).2 hsys) hb hconv

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u → pairM (coX t b c u) (coY σ X Y t b c u) = 0 →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      (∀ ι, M.IsLinW ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (pairM Z (coY σ X Y t b c u)) * ι φ (Z + coX t b c u)) ∧
      ∀ ι, M.IsLinBar ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (-pairM Z (coX t b c u)) * ι φ (Z + coY σ X Y t b c u) := by
  first | exact @GlobalTheory.HeisFlip.heis_trans_char | exact GlobalTheory.HeisFlip.heis_trans_char | (intros; apply GlobalTheory.HeisFlip.heis_trans_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  first | exact @GlobalTheory.SplitDblNab.nMat_mem_NabD | exact GlobalTheory.SplitDblNab.nMat_mem_NabD | (intros; apply GlobalTheory.SplitDblNab.nMat_mem_NabD <;> assumption)
end

