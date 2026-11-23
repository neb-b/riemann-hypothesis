module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubOneMemPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

open Classical

namespace GlobalTheory.ValUnitLevel
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit Formalism.L2.Host GlobalTheory.ValUnit

theorem isUnit_mk_pow {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {a : R} (ha : a ∉ P) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (P ^ n) a) := by
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv ha
  have hnil : IsNilpotent (Ideal.Quotient.mk (P ^ n) i) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi n⟩
  have h1 : Ideal.Quotient.mk (P ^ n) y * Ideal.Quotient.mk (P ^ n) a = 1 - Ideal.Quotient.mk (P ^ n) i := by
    rw [← map_mul, eq_sub_iff_add_eq, ← map_add (f := _), e, map_one]
  exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)

theorem exists_pow_sub_one_mem_pow {L : Type} [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) (a : 𝓞 L)
    (n : HeightOneSpectrum (𝓞 L) → ℕ) (ha : ∀ w ∈ S, a ∉ w.asIdeal) :
    ∃ M : ℕ, 0 < M ∧ ∀ w ∈ S, a ^ M - 1 ∈ w.asIdeal ^ n w := by
  have key : ∀ w ∈ S, ∃ m : ℕ, 0 < m ∧ Ideal.Quotient.mk (w.asIdeal ^ n w) a ^ m = 1 := fun w hw => by
    haveI : Finite (𝓞 L ⧸ w.asIdeal ^ n w) :=
      Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
    obtain ⟨u, hu⟩ := isUnit_mk_pow w.isMaximal (ha w hw) (n w)
    obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite u)
    exact ⟨m, hm, by rw [← hu]; simpa using congrArg Units.val e⟩
  choose! m hm e using key
  refine ⟨∏ w ∈ S, m w, Finset.prod_pos hm, fun w hw => ?_⟩
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← Finset.mul_prod_erase _ _ hw, pow_mul, e w hw, one_pow]

theorem locK_eq_one_of_levelLe {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {w : HeightOneSpectrum (𝓞 L)}
    {n : ℕ} (h : χ.LevelLe w n) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a) (ha0 : a ∉ w.asIdeal)
    (ha : a - 1 ∈ w.asIdeal ^ n) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk]
    exact w.intValuation_eq_one_iff.2 ha0
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1)) := by
      rw [map_sub, map_sub, map_one, map_one]
      congr 1
      show algebraMap L (w.adicCompletion L) (k : L) = _
      rw [hk]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a - 1))) =
        w.valuation L (algebraMap (𝓞 L) L (a - 1)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2, w.valuation_of_algebraMap, w.intValuation_le_pow_iff_mem]
    exact ha

theorem unitOff_val : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (I : Type) [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ) (v : HeightOneSpectrum (𝓞 L)) (q : ℕ), χ.HasInf φ n → χ.UnrAt v →
    (q : 𝓞 L) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q ((χ.val v : ℂˣ) : ℂ) := by
  intro L _ _ χ I _ φ n v q hinf hv hq
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose nl hnl using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · exact ⟨Units.ne_zero _, 1, by simpa using isIntegral_zero, by simpa using isIntegral_zero⟩
  obtain ⟨h, a, hh, ha0, ha⟩ := exists_pow_eq_span v
  have hav : a ∈ v.asIdeal := Ideal.pow_le_self hh.ne' (ha ▸ Ideal.mem_span_singleton_self a)
  have haw : ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → a ∉ w.asIdeal := fun w hw hm => by
    have h1 : v.asIdeal ^ h ≤ w.asIdeal := by rw [ha, Ideal.span_singleton_le_iff_mem]; exact hm
    have h2 : v.asIdeal ≤ w.asIdeal := fun x hx => w.isPrime.mem_of_pow_mem h (h1 (Ideal.pow_mem_pow hx h))
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)
  obtain ⟨b, hb⟩ : a ∣ (q : 𝓞 L) ^ h := Ideal.mem_span_singleton.1 (ha ▸ Ideal.pow_mem_pow hq h)
  have hvS : v ∉ hfin.toFinset := by simpa using hv
  have hne : ∀ w ∈ hfin.toFinset, w ≠ v := fun w hw e => hvS (e ▸ hw)
  obtain ⟨M, hM, hM1⟩ := exists_pow_sub_one_mem_pow hfin.toFinset a nl fun w hw => haw w (hne w hw)
  have hc0 : a ^ M ≠ 0 := pow_ne_zero _ ha0
  have hk0 : ((a ^ M : 𝓞 L) : L) ≠ 0 := by exact_mod_cast hc0
  set k : Lˣ := Units.mk0 _ hk0 with hk
  have hord : ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = -WithZero.log (w.intValuation (a ^ M)) := fun w => by
    show -WithZero.log (w.valuation L (algebraMap (𝓞 L) L (a ^ M))) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hp := GlobalTheory.TypeValues.productRule χ hfin.toFinset (fun w hw => by simpa using hw) k
  rw [Finset.prod_eq_one (fun w hw => locK_eq_one_of_levelLe (hnl w) k (a ^ M) rfl
      (fun hm => haw w (hne w hw) (w.isPrime.mem_of_pow_mem M hm)) (hM1 w hw)), mul_one,
    finprod_eq_single _ v (fun w hw => by
      rw [hord, HeightOneSpectrum.intValuation_eq_one_iff.2 (fun hm => haw w hw (w.isPrime.mem_of_pow_mem M hm))]
      simp), finprod_eq_if, if_pos hvS] at hp
  have hpos : 0 < ordF v k := by
    rw [hord]
    have h0 : v.intValuation (a ^ M) ≠ 0 := v.intValuation_ne_zero _ hc0
    have h3 := (v.intValuation_le_pow_iff_mem (a ^ M) 1).2 (by
      rw [pow_one]; exact Ideal.pow_mem_of_mem _ hav M hM)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  rw [he, zpow_natCast] at hp
  refine unitOff_of_pow (k := e) (by omega) ?_
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, hinf] at hp'
  rw [eq_inv_of_mul_eq_one_right hp']
  refine unitOff_inv (unitOff_prod _ _ fun i _ => unitOff_zpow (unitOff_div_norm ?_) _)
  have hi : ∀ x : 𝓞 L, IsIntegral ℤ (φ i (algebraMap (𝓞 L) L x)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map (φ i).toIntAlgHom
  show UnitOff q (φ i (algebraMap (𝓞 L) L (a ^ M)))
  rw [map_pow, map_pow]
  refine unitOff_pow (unitOff_of_mul_eq (m := h) (hi a) (hi b) ?_ hq0.ne') M
  rw [← map_mul, ← map_mul, ← hb, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.ValUnitLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentation
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TypeVec

section Gen

theorem isIrreducible_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H' X) (f : H →* H') (hf : Function.Surjective f) (hτ : τ.IsIrreducible) :
    Representation.IsIrreducible (τ.comp f) := by
  let e : Subrepresentation (τ.comp f : Representation ℂ H X) ≃o Subrepresentation τ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).2 hτ

def glMap {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    GL (Fin n) K →* GL (Fin m) K' :=
  (Units.map (Matrix.reindexAlgEquiv K' K' (finCongr h.symm)).toAlgHom.toRingHom.toMonoidHom).comp
    (Matrix.GeneralLinearGroup.map e.toRingHom)

theorem glMap_apply {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin n) K) (i j : Fin m) : (glMap e h g).1 i j = e (g.1 (Fin.cast h i) (Fin.cast h j)) := rfl

theorem glMap_symm {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin m) K') : glMap e h (glMap e.symm h.symm g) = g := by
  apply Units.ext
  ext i j
  rw [glMap_apply, glMap_apply]
  simp

theorem glMap_surjective {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    Function.Surjective (glMap e h) := fun g => ⟨glMap e.symm h.symm g, glMap_symm e h g⟩

theorem mem_fixed_iff {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X}
    {K : Subgroup H} {x : X} : x ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

end Gen

variable {D : D7}

def typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible) :
    TypeDataG V where
  S := S
  frame := s
  W := fun w => Fin (n (pl w)) → ℂ
  τ := fun w => (τ (pl w)).comp (glMap (ρv w) hr)
  irred := fun w => isIrreducible_comp _ _ (glMap_surjective _ _) (hτ (pl w))

theorem noFixed_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    (hne : S.Nonempty)
    (h : ∀ a, 0 < a → a < V.rank → ∃ v : S, ∀ y : Fin (n (pl v)) → ℂ,
      (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF v.1) V.rank a, τ (pl v) (glMap (ρv v) hr g) y = y) → y = 0) :
    NoFixed (typeOf hr S pl s ρv n τ hτ) :=
  ⟨hne, h⟩

theorem hasTypeVec_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W) (hx : x ≠ 0)
    (hoff : ∀ v ∉ S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x)
    (hon : ∀ v : S, x ∈ Submodule.span ℂ {y | ∃ φ : (Fin (n (pl v)) → ℂ) →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (τ (pl v) (glMap (ρv v) hr ((s v).red k)) z) = σ (locFin V v k) (φ z)) ∧
        y ∈ LinearMap.range φ}) :
    HasTypeVec (typeOf hr S pl s ρv n τ hτ) σ :=
  ⟨x, hx, hoff, hon⟩


set_option maxHeartbeats 1000000 in
theorem hasTypeVec_of_goodRep : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F hF W _ _ σ _hadm hgood
  classical
  have hrk : (Yc D 0).rank = D.R.r := by rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hlev := hF.core.lev
  obtain ⟨c0, hbase⟩ := hlev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hnc : ∀ PP ∈ (R.dat0 R.triv).Pg, ∀ PP' ∈ (R.dat0 R.triv).Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP hP PP' hP'
    obtain ⟨k, hk⟩ := (hlev.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (hlev.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.PrinFixedRep.main D (Yc D 0) (R.βY 0) (R.dat0 R.triv) (GlobalTheory.ProjectedLift.liftsExist_rows R hlev) W σ
  obtain ⟨v, hv0, hvK, κ, hκ, hve⟩ := hgood
  have hvmem : v ∈ GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))) :=
    mem_fixed_iff.2 fun k => hvK _ (Subgroup.mem_subgroupOf.1 k.2)
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  have hfix : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • ρ (R.eG g) ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hve
    rw [SetLike.val_smul, hρ (R.eG g) (κ g) (hκ g)]
  obtain ⟨U, hUfd, hUirr, y, hy0, hye⟩ := _root_.GlobalTheory.FixedVec.exists_irreducible_subrep_fixed _ _ _ ρ (fun g => R.eG g) _ ⟨v, hvmem⟩
    (fun h => hv0 (congrArg Subtype.val h)) hfix
  haveI := hUfd
  have hH := GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H hGC R F hF U.toSubmodule U.toRepresentation hUirr ⟨y, hy0, hye⟩
  choose n τ hτ hrest using _root_.GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi (↥R.Pg) (fun PP => GL (Fin D.R.r) (kP PP.1)) U.toSubmodule U.toRepresentation hUirr
  obtain ⟨a, S, pl, s, ρv, hoff, hon⟩ : ∃ (a : GfC (Yc D 0)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ R.Pg)
      (s : ∀ v : S, SplitAt D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) v) (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1),
      (∀ v ∉ S, ∀ k ∈ Kv (Yc D 0) v, ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∈
        levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) ∧
      ∀ (v : S) (k : Kv (Yc D 0) v), ∃ g0 : G0 R.Pg D.R.r, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0
          ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∧
        (∀ PP, PP ≠ pl v → g0 PP = 1) ∧
        ∀ i j : Fin D.R.r, (g0 (pl v)).1 i j = ρv v (((s v).red k).1 (i.cast hrk.symm) (j.cast hrk.symm)) :=
    _root_.GlobalTheory.TrPtFrame.exists_splitFrame_levG D (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hrk.symm hbase rfl hnc

  let yW : W := (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)
  have hyK : ∀ h : ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))), σ h yW = yW := mem_fixed_iff.1 (y : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).2

  have hcomm : ∀ (l : GfC (Yc D 0)) (q : W), σ a⁻¹ (σ (a * l * a⁻¹) q) = σ l (σ a⁻¹ q) := by
    intro l q
    have e1 : σ a⁻¹ * σ (a * l * a⁻¹) = σ l * σ a⁻¹ := by
      rw [← map_mul, ← map_mul, show a⁻¹ * (a * l * a⁻¹) = l * a⁻¹ by group]
    exact congrArg (fun f : Module.End ℂ W => f q) e1
  have hconj : ∀ l : GfC (Yc D 0), σ (a * l * a⁻¹) yW = yW → σ l (σ a⁻¹ yW) = σ a⁻¹ yW :=
    fun l hl => (hcomm l yW).symm.trans (congrArg (σ a⁻¹) hl)
  refine ⟨typeOf hrk.symm S pl s ρv n τ hτ, noFixed_typeOf _ _ _ _ _ _ _ _ ?_ ?_,
    hasTypeVec_typeOf _ _ _ _ _ _ _ _ σ (σ a⁻¹ yW) ?_ ?_ ?_⟩
  · obtain ⟨PP, -⟩ := hH 1 one_pos (by omega)
    exact ⟨(pl.symm PP).1, (pl.symm PP).2⟩
  · intro b hb hbr
    obtain ⟨PP, hPP⟩ := hH b hb (lt_of_lt_of_eq hbr hrk)
    refine ⟨pl.symm PP, fun z hz => ?_⟩
    obtain ⟨⟨φ, hφi, hφ⟩, -⟩ := hrest (pl (pl.symm PP))
    have hpl : pl (pl.symm PP) = PP := pl.apply_symm_apply PP
    rw [← hpl] at hPP
    apply hφi
    refine Eq.trans ?_ (map_zero φ).symm
    apply hPP
    rintro u ⟨hu1, hu2⟩
    have e1 := hφ (u (pl (pl.symm PP))) z
    have hmem : glMap (ρv (pl.symm PP)).symm hrk (u (pl (pl.symm PP))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF (pl.symm PP).1) (Yc D 0).rank b := by
      intro i j hij
      rw [glMap_apply]
      have hent : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) =
          (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP (pl (pl.symm PP)).1)) (Fin.cast hrk i) (Fin.cast hrk j) := by
        by_contra hne
        exact hij (hu2 _ _ hne)
      by_cases hij' : i = j
      · subst hij'
        have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk i) = 1 := by simpa using hent
        simp only [h1, map_one, Matrix.one_apply_eq]
      · have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) = 0 := by
          rw [hent, Matrix.one_apply_ne (fun h => hij' (Fin.cast_injective hrk h))]
        simp only [h1, map_zero, Matrix.one_apply_ne hij']
    have h2 := hz _ hmem
    rw [glMap_symm] at h2
    refine Eq.trans ?_ (congrArg φ h2)
    refine Eq.trans ?_ e1.symm
    refine congrArg (fun g => U.toRepresentation g (φ z)) ?_
    funext P'
    by_cases h : P' = pl (pl.symm PP)
    · subst h
      exact (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).symm
    · exact (hu1 P' h).trans (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) h _).symm
  · intro h0
    apply hy0
    have h1 : yW = 0 := by
      have := congrArg (σ a) h0
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at this
    exact Subtype.ext (Subtype.ext h1)
  · intro w hw k hk
    exact hconj _ (hyK ⟨_, Subgroup.mem_subgroupOf.2 (hoff w hw k hk)⟩)
  · intro w
    obtain ⟨-, hsp⟩ := hrest (pl w)
    have hkey : ∀ (k : Kv (Yc D 0) w) (q : U.toSubmodule),
        σ a⁻¹ ((((U.toRepresentation (Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k))) q) :
          U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) =
          σ (locFin (Yc D 0) w k) (σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) := by
      intro k q
      have h2 := hon w k
      have hlift := h2.choose_spec.1
      have hone := h2.choose_spec.2.1
      have hent := h2.choose_spec.2.2
      have hg0 : Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k)) = h2.choose := by
        funext P'
        by_cases hP : P' = pl w
        · subst hP
          refine (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).trans ?_
          apply Units.ext
          ext i j
          exact (glMap_apply _ _ _ i j).trans (hent i j).symm
        · exact (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) hP _).trans (hone P' hP).symm
      have e2 := hρ _ (a * locFin (Yc D 0) w k * a⁻¹) hlift (q : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))))
      exact (congrArg (fun g => σ a⁻¹ ((((U.toRepresentation g q) : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) hg0).trans
        ((congrArg (σ a⁻¹) e2).trans (hcomm _ _))
    have hy := Submodule.eq_top_iff'.1 hsp y
    show σ a⁻¹ (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) ∈ _
    clear hconj hyK yW hye hy0
    induction hy using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨ψ, hψ, z, rfl⟩ := hu
      exact Submodule.subset_span ⟨(σ a⁻¹ ∘ₗ (GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).subtype ∘ₗ U.toSubmodule.subtype) ∘ₗ ψ,
        fun k z' => (congrArg (fun q : U.toSubmodule => σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W))
          (hψ _ z')).trans (hkey k (ψ z')), z, rfl⟩
    | zero => simpa using zero_mem _
    | add u u' _ _ hu hu' => simpa only [Submodule.coe_add, map_add (f := _)] using add_mem hu hu'
    | smul c u _ hu => simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ c hu

end GlobalTheory.TypeVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore _root_.GlobalTheory.exists_isotropic_graph_isUnit_lowerRow F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizer
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.ResidueEisenstein

theorem finCovol_leviOne_last : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW π DM hπ hDM
  obtain ⟨m, Z, J₀, hF⟩ := _root_.GlobalTheory.FrameExt.exists_fr F E σ n J r X Y hcm hJ hW
  letI : MeasurableSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set A := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hA
  set G₁ := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker
  set ΓA := (ratPts σ J).subgroupOf A
  set ΓG := (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range.subgroupOf G₁
  obtain ⟨hlc, hsc, hdisc, hfinGL⟩ := GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume F E σ hcm (r + 1)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv F E σ n J r m X Y Z J₀ hF
  have hclA : IsClosed (A : Set (GAd σ J)) :=
    (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const).inter
      (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const)
  haveI : LocallyCompactSpace A := hclA.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) :=
    (GlobalTheory.StdPar.isClosed_levi _ hcm hJ hW).2.locallyCompactSpace
  haveI := hlc
  haveI := hsc
  haveI := hdisc
  haveI : DiscreteTopology ΓA := DiscreteTopology.of_continuous_injective
    (f := fun x : ΓA => (⟨(x.1 : GAd σ J), x.2⟩ : ratPts σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ratPts σ J => (y : GAd σ J)) h)
  haveI : Countable (ΓA.prod ΓG) := by
    haveI : Countable ΓA := inferInstance
    haveI : Countable ΓG := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Function.Injective.countable (f := fun x : ΓA.prod ΓG => ((⟨x.1.1, x.2.1⟩ : ΓA), (⟨x.1.2, x.2.2⟩ : ΓG)))
      (fun a b h => Subtype.ext (Prod.ext (congrArg (fun q => (q.1 : A)) h) (congrArg (fun q => (q.2 : G₁)) h)))
  refine GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv (A × G₁) _ φ (ΓA.prod ΓG) _ (fun g => ?_)
    (fun μ hμ 𝓕 h𝓕 => _root_.GlobalTheory.measure_fundamentalDomain_prod_lt_top A G₁ ΓA ΓG
      (fun μ hμ 𝓕 h𝓕 => _root_.GlobalTheory.SphEis.finCovol_fixG F E σ n J (r + 1) m X Y Z J₀ hF μ 𝓕 hμ h𝓕) (fun μ hμ 𝓕 h𝓕 => hfinGL μ 𝓕 hμ h𝓕)
      μ hμ 𝓕 h𝓕) π DM hπ hDM
  rw [Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ g]

end GlobalTheory.ResidueEisenstein
end

