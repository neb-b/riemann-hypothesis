module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OnePrimeEach

theorem exists_ratPrime_mem {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ w.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem exists_mem_of_prime (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ P.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 L)).injective_int]; exact bot_le)
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ']
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) (Ideal.mem_bot.1 hmem)

theorem ratPrime_unique {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpw : (p : 𝓞 L) ∈ w.asIdeal) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 L))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hqw)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def ratP (v : HeightOneSpectrum (𝓞 H.F)) : ℕ := (exists_ratPrime_mem v).choose

theorem ratP_prime (v : HeightOneSpectrum (𝓞 H.F)) : (ratP H v).Prime := (exists_ratPrime_mem v).choose_spec.1

theorem ratP_mem (v : HeightOneSpectrum (𝓞 H.F)) : ((ratP H v : ℕ) : 𝓞 H.F) ∈ v.asIdeal :=
  (exists_ratPrime_mem v).choose_spec.2

theorem ratP_eq (v : HeightOneSpectrum (𝓞 H.F)) {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ratP H v = p := ratPrime_unique v (ratP_prime H v) hp (ratP_mem H v) h

def primeK (p : ℕ) : HeightOneSpectrum (𝓞 H.K) :=
  if hp : p.Prime then (exists_mem_of_prime H.K hp).choose else (exists_mem_of_prime H.K Nat.prime_two).choose

theorem primeK_mem {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 H.K) ∈ (primeK H p).asIdeal := by
  unfold primeK
  rw [dite_eq_left hp]
  exact (exists_mem_of_prime H.K hp).choose_spec

def sel (v : HeightOneSpectrum (𝓞 H.F)) : HeightOneSpectrum (𝓞 H.E) :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose

theorem sel_mem (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ PvSet H (primeK H (ratP H v)) v :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose_spec

theorem sel_above (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ aboveF (L := H.E) H.F v := (sel_mem H v).1

theorem sel_under (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.F) = v := by
  have h := sel_above H v
  rw [aboveF, Set.Finite.mem_toFinset] at h
  exact h

theorem sel_underK (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.K) = primeK H (ratP H v) := (sel_mem H v).2

theorem sel_mem_of {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    sel H v ∈ PvSet H (primeK H p) v := by
  have h := sel_mem H v
  rwa [ratP_eq H v hp hv] at h

def splitPlacesTwoPrimes : PlacesOverCommonPrime H :=
  ⟨primeK H H.pde, primeK H H.pde', primeK_mem H H.pde_prime, primeK_mem H H.pde'_prime, fun v _ => sel H v,
    fun v _ => sel H v, fun v hv => sel_mem_of H H.pde_prime v hv, fun v hv => sel_mem_of H H.pde'_prime v hv⟩

end GlobalTheory.Mem.Top.Bl.OnePrimeEach


open GlobalTheory.Mem.Top.Bl.OnePrimeEach in
theorem GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  intro B
  refine ⟨sel B.host, splitPlacesTwoPrimes B.host, ?_, sel_above B.host, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro v
    exact congrArg HeightOneSpectrum.asIdeal (sel_under B.host v)
  · intro v v' p hp hv hv'
    rw [sel_underK, sel_underK, ratP_eq B.host v hp hv, ratP_eq B.host v' hp hv']

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilTwist

variable {D : D7}

theorem exists_isDetRoot (V : HSp D) (g : GA D V) : ∃ x, IsDetRoot V g x := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V 1 (isHC_one D).1 (fun _ => rfl)
  exact aval.1 g

theorem twist_both {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D}
    (ha : AdmE V W χ χ') (hν : IsHC D ν) (rν : ResEta D ν 0) (hν' : IsHC D ν') (rν' : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ho : IsWeilOn ψ V W χ χ' om)
    (ho' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g : GA D V} {h : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((ν' x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) := by
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.Mem.HeckeExp.hecke_exp_laws D
  have hmul : ∀ a b : IdC D, IsHC D a → IsHC D b → IsHC D (a * b) := fun a b k l =>
    (hC _).1 (C.mul_mem ((hC _).2 k) ((hC _).2 l))
  have ha' : AdmE V W (χ * ν) (χ' * ν') :=
    ⟨ha.1, hmul _ _ ha.2.1 hν, hmul _ _ ha.2.2.1 hν', resEta_mul ha.2.2.2.1 rν, resEta_mul ha.2.2.2.2 rν'⟩
  obtain ⟨o, hd, ht⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha ho
  obtain ⟨o', hd', ht'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W _ _ om' ha' ho'
  obtain ⟨o'', hd'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o hd hν.1 hν'.1 rν rν'
  obtain ⟨e, -, -, he, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  have hΦ : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simp only [← he]
    exact (hth ψ _).2 (mem_ThS.1 Φ.2)
  have k := _root_.GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ V W _ _ o' o'' hd' hd'' (g, h) _ hΦ
  rw [ht', hv g h x y hx hy, LinearMap.smul_apply, ht] at k
  have k2 := congrFun k (e.symm w)
  simp only [← he, e.apply_symm_apply, Pi.smul_apply] at k2
  exact k2

theorem weilTwEq : ∀ D : D7, WeilTwEq D := by
  intro D ψ hψ V W χ χ' ν ha hν rν om ho
  have r1 : ResEta D 1 0 := ⟨rν.1, fun _ _ _ => by simp⟩
  refine ⟨fun om' ho' g h x hx => ?_, fun om' ho' g h x hx => ?_⟩
  · obtain ⟨y, hy⟩ := exists_isDetRoot W h
    have := twist_both hψ ha (isHC_one D) r1 hν rν ho (om' := om') (by rwa [mul_one]) hx hy
    rwa [MonoidHom.one_apply, mul_one] at this
  · obtain ⟨y, hy⟩ := exists_isDetRoot V g
    have := twist_both hψ ha hν rν (isHC_one D) r1 ho (om' := om') (by rwa [mul_one]) hy hx
    rwa [MonoidHom.one_apply, inv_one, one_mul] at this

end GlobalTheory.Mem.WeilTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Col2.RatFrPt
open GlobalTheory.Mem.Col2.PtExist

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def glEquiv (γ : GL (Fin n) E) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (γ : Matrix (Fin n) (Fin n) E)) (Matrix.toLin' ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem glEquiv_apply (γ : GL (Fin n) E) (x : Sp E n) : glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

theorem glEquiv_single (γ : GL (Fin n) E) (i j : Fin n) : glEquiv γ (Pi.single j 1) i = (γ : Matrix (Fin n) (Fin n) E) i j := by
  rw [glEquiv_apply, Matrix.mulVec_single_one]
  rfl

theorem adAt_inv {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (r s : Fin n) : adAt F P (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) r s) := by
  set M : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) with hM
  have hM' : M = (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) := Matrix.ext fun a b => h a b
  have h1 : ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) * M = 1 := by
    rw [hM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) * M = 1 := by
    rw [hM', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e := (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)
  exact congrFun (congrFun e r) s

variable [StarRing E]

theorem glEquiv_mem_iff {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (hN : IsSdLat (Formalism.UG.CS.globLat g (stdLat E n)))
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (x : Sp E n) : glEquiv γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g (stdLat E n)) ↔ x ∈ stdAt E n P := by
  have hi := adAt_inv h
  constructor
  · intro hx
    rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
    intro i
    have h1 := valued_pullV_le g hx i
    have e : adAt F P (Formalism.L2.Col.pullV g (glEquiv γ x) i) = algebraMap E (P.adicCompletion E) (x i) := by
      have e2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ glEquiv γ x = x := by
        rw [glEquiv_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      conv_rhs => rw [← e2]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, hi, adAt_inclE]
    rwa [e] at h1
  · intro hx
    obtain ⟨f, hf⟩ := CharValCompare.exists_isFr P hN
    have hy : f.symm (glEquiv γ x) ∈ stdAt E n P := by
      rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
      intro i
      set A : Matrix (Fin n) (Fin n) E := mat f.symm * (γ : Matrix (Fin n) (Fin n) E) with hA
      have hA1 : ∀ j, Valued.v (algebraMap E (P.adicCompletion E) (A i j)) ≤ 1 := by
        intro j
        have hmem : (fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l j) ∈
            Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat g (stdLat E n)) := by
          apply (carries_globLat g _).2
          apply (mem_latS_std _).2
          intro l
          simp only [Matrix.mulVec, dotProduct]
          rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
        have h2 := valued_symm_le (u := fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l j) hf
          hmem i
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [h, ← map_mul, ← map_sum] at h2
        rw [hA, Matrix.mul_apply]
        exact h2
      have e3 : f.symm (glEquiv γ x) = A *ᵥ x := by
        funext i
        rw [← mat_mulVec, hA, ← Matrix.mulVec_mulVec, glEquiv_apply]
        rfl
      rw [e3]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul]
      exact mul_le_one' (hA1 j) ((GlobalTheory.Mem.ColAd.mem_stdAt_val.1 hx) j)
    have := (hf _).2 hy
    rwa [f.apply_symm_apply] at this
end

theorem exists_isPtOf_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g hg hQ
  choose! γ hγ using hQ
  obtain ⟨p₀, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p₀.deco.1.N := congrArg Deco.N hd
  have hlat : IsSdLat (Formalism.UG.CS.globLat g (stdLat E n)) :=
    hN ▸ ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩
  let p : DecoF E n ST SG Q := ⟨(p₀.deco, fun P => glEquiv (γ P.1)), fun P x => by
    show glEquiv (γ P.1) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p₀.deco.1.N ↔ _
    rw [← hN]
    exact glEquiv_mem_iff hlat (hγ P.1 P.2) x⟩
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.f P v)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.be P v i)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · show _ = algebraMap E _ (glEquiv (γ P.1) (Pi.single j 1) i)
    rw [glEquiv_single]
    exact hγ P.1 P.2 i j

end GlobalTheory.Mem.Col2.RatFrPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.ChainLevel


set_option maxHeartbeats 4000000 in
theorem chain_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  obtain ⟨jX, hjX, htop⟩ := _root_.GlobalTheory.TopRead.top_read D G Pl0 I0 T A3 Ks R F cG hI hP hH y b m s tA hA
  obtain ⟨EE, Mult, mZ, mT, io, jE, jM, hEi, hEr, hEip, hM, hio0, hio, hioT, hjunk⟩ :=
    _root_.GlobalTheory.ChainHilb.exists_chainHilb D (y.C F.lv2) b y.Us (fun μ => (s μ).A) jX D.R.two_le_m (h1 b).1 (h1 b).2 (h2 b) hjX
  obtain ⟨hsup, horth⟩ := _root_.GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hR b
  classical
  haveI : Finite Φ := hR.fin
  haveI : Fintype Φ := Fintype.ofFinite Φ
  have hle : ∀ π, y.prtE F.lv2 b (rep π) ≤ LinearMap.range jE := fun π => hEr ▸ hsup ▸ le_iSup (fun π => y.prtE F.lv2 b (rep π)) π
  let p : Φ → Submodule ℂ EE.T := fun π => (y.prtE F.lv2 b (rep π)).comap jE
  have hmap : ∀ π, (p π).map jE = y.prtE F.lv2 b (rep π) := fun π => Submodule.map_comap_eq_of_le (hle π)
  have hptop : (⨆ π, p π) = ⊤ := by
    apply Submodule.map_injective_of_injective hEi
    rw [Submodule.map_iSup, Submodule.map_top, hEr]
    simp only [hmap]
    exact hsup
  have hporth : ∀ π π', π ≠ π' → p π ⟂ p π' := by
    intro π π' hne
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [hEip]
    exact horth π π' hne _ hu _ hv
  obtain ⟨bs, ty, hft⟩ := GlobalTheory.Mem.exists_orthonormalBasis_adapted EE.T Φ p hptop hporth
  have hdisj : ∀ π π', π ≠ π' → y.prtE F.lv2 b (rep π) ⊓ y.prtE F.lv2 b (rep π') = ⊥ := by
    intro π π' hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hxE : x ∈ (y.C F.lv2).EEc b := hEr ▸ hle π hx1
    have h0 := horth π π' hne x hx1 x hx2
    by_contra hne0
    have := (h1 b).1.pos ⟨x, hxE⟩ (fun h => hne0 (by simpa using congrArg Subtype.val h))
    rw [h0] at this
    simp at this
  exact ⟨⟨EE, Mult, mZ, mT, io, _, bs, ty⟩, ⟨jE, jM, jX, hEi, hEr, hEip, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).1,
    fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.1, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.2,
    fun μ hμ => (hjX μ hμ).1, fun μ hμ => (hjX μ hμ).2.1, fun μ hμ => (hjX μ hμ).2.2, hio0, hio, hioT, hjunk,
    hft, hdisj, htop⟩⟩

end GlobalTheory.Mem.R3.Rw.ChainLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMap
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtId.OneScalar

theorem map_pG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c c' : Coeff l) (φ : c.F →+* ℂ) (φ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    MvPolynomial.map φ (pG (Dw := Dw) c a n) = MvPolynomial.map φ' (pG (Dw := Dw) c' a n) := by
  have h : ∀ s i hi col, MvPolynomial.map φ (minorPolynomial (Dw := Dw) (n := n) c s i hi col) =
      MvPolynomial.map φ' (minorPolynomial c' s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero, map_zero]

theorem ten_extremal_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (Formalism.L2.DIV.ten fun τ => extremal K n (lam τ)) ∈ Formalism.L2.DIV.VV K lam :=
  GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam τ))

theorem lt_injective {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (hH : ∀ ρ, tauE D ρ (H.rt : D.host.E) = H.rt0)
    {m n : ℕ} (lt : LtN Dw n → FVar D m n)
    (hlt : ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
      (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))) : Function.Injective lt := by
  have hp : ∀ ℓ : LtN Dw n, ∀ ρ, ℓ.1 = tauE D ρ → (ℓ.2.1 : ℕ) < Dw.p := by
    rintro ⟨σ, s, b⟩ ρ h
    have hs := s.2
    have : Dw.mult σ = Dw.p := by
      rw [show σ = tauE D ρ from h]
      exact if_pos (hH ρ)
    exact this ▸ hs
  intro x y hxy
  obtain ⟨a1, a2⟩ := hlt x
  obtain ⟨b1, b2⟩ := hlt y
  have hpx := hp x (lt x).1
  have hpy := hp y (lt y).1
  rw [hxy] at a1 a2 hpx
  have key : x.1 = y.1 ∧ (x.2.1 : ℕ) = y.2.1 := by
    rcases a2 with ⟨a2, a3⟩ | ⟨a2, a3⟩ <;> rcases b2 with ⟨b2, b3⟩ | ⟨b2, b3⟩
    · exact ⟨a2.trans b2.symm, by omega⟩
    · have := hpx a2; omega
    · have := hpy b2; omega
    · exact ⟨a2.trans b2.symm, by omega⟩
  obtain ⟨σ, s, b⟩ := x
  obtain ⟨σ', s', b'⟩ := y
  obtain ⟨k1, k2⟩ := key
  dsimp only at k1 k2 a1 b1
  subst k1
  obtain rfl : s = s' := Fin.ext k2
  obtain rfl : b = b' := a1.symm.trans b1
  rfl

section Hw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem coefficientMap_extremalTensor_baseChange {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw)
    {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0') :
    O.c0' O.hw = c0L ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩ := by
  obtain ⟨v', h1, h2⟩ := hc ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [h1, show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

end Hw

end GlobalTheory.PtId.OneScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  first | exact @GlobalTheory.Mem.Col2.Splice.isPtOf_splice | exact GlobalTheory.Mem.Col2.Splice.isPtOf_splice | (intros; apply GlobalTheory.Mem.Col2.Splice.isPtOf_splice <;> assumption)
end

