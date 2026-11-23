module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOneOfChrEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open Formalism.L2.Host

variable {D : D7} {T N : Type}

theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

end GlobalTheory.ConjExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourier
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatFourierQ

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_prod' {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_dvd {N q m : ℕ} {C : ℂ} (hq : q ∣ N) (h0 : C ≠ 0) (hC : IsIntegral ℤ C)
    (hCq : IsIntegral ℤ ((q : ℂ) ^ m * C⁻¹)) : UnitOff N C := by
  obtain ⟨d, rfl⟩ := hq
  have hint : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine ⟨h0, m, ((hint _).pow m).mul hC, ?_⟩
  have e : ((q * d : ℕ) : ℂ) ^ m * C⁻¹ = (d : ℂ) ^ m * ((q : ℂ) ^ m * C⁻¹) := by push_cast; ring
  rw [e]; exact ((hint d).pow m).mul hCq

theorem dite_prod' {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_eq_unit_mul_flat_transform : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  intro D _ Q ξ ψP r n N _ hQ
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  have hloc : ∀ PP : ↥Q, ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧
      IsIntegral ℤ ((Nat.card (kP PP.1) : ℂ) ^ m * C⁻¹) ∧
      ∀ u : Matrix (Fin n) (Fin r) (kP PP.1),
        (∑ y : Matrix (Fin r) (Fin n) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C * fq PP.1 u := by
    intro PP
    letI := Ideal.Quotient.field PP.1.asIdeal
    obtain ⟨C, m, h0, h1, h2, h3⟩ :=
      _root_.GlobalTheory.fourier_flatDatum_finite (kP PP.1) (ψP PP.1) (ξ PP.1) r n (hQ _ PP.2).1 (hQ _ PP.2).2.1
    exact ⟨C, m, h0, h1, by rw [Nat.card_eq_fintype_card]; exact h2, h3⟩
  choose C m hC0 hCi hCm hCe using hloc
  refine ⟨(∏ PP : ↥Q, C PP)⁻¹, ?_, fun ub => ?_⟩
  · have hu : UnitOff N (∏ PP : ↥Q, C PP) :=
      unitOff_prod' _ _ fun PP _ => unitOff_of_dvd (hQ _ PP.2).2.2 (hC0 PP) (hCi PP) (hCm PP)
    obtain ⟨h0, e, h1, h2⟩ := hu
    exact ⟨inv_ne_zero h0, e, h2, by rw [inv_inv]; exact h1⟩
  · have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
      rw [← Finset.attach_eq_univ]
      unfold omegaQ
      convert dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
      intro y
      have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP),
          omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
        intro Y
        unfold omegaFlat
        convert dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
      rw [e0, Finset.attach_eq_univ]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [dif_pos PP.2, Subtype.coe_eta]
    simp only [hf, ← Finset.prod_mul_distrib]
    have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin n) (kP PP.1))))
      (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin n) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
    rw [Fintype.piFinset_univ] at hs
    rw [← hs]
    simp only [hCe]
    rw [Finset.prod_mul_distrib, hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatFourierQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndepende
section
namespace GlobalTheory.ConjSpan

theorem exists_ringEquiv_fix_ne (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : Transcendental ℚ z) : ∃ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) ∧ τ z ≠ z := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq (fun q => by simp)
  have hzK : Transcendental K z := fun h => hz (h.restrictScalars ℚ)
  have hind : AlgebraicIndepOn K id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hzK
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let n : MvPolynomial B K ≃ₐ[K] MvPolynomial B K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => - MvPolynomial.X i)
      (MvPolynomial.aeval fun i => - MvPolynomial.X i) (by ext; simp) (by ext; simp)
  let e := hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv, ?_, ?_⟩
  · intro x
    have hx : σ x = algebraMap K ℂ x := rfl
    rw [hx, IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have h2 : IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩))
        = hB.1.aevalEquiv (- MvPolynomial.X ⟨z, hzB'⟩) := by
      simp [e, n]
    rw [this, map_neg, map_neg, h1]
  rw [h2]
  intro h
  have hz0 : z = 0 := by linear_combination (-1/2 : ℂ) * h
  exact hz (hz0 ▸ isAlgebraic_zero)

theorem exists_eq_of_forall_fixed (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) → τ z = z) : ∃ c : K, σ c = z := by
  by_cases ha : IsAlgebraic ℚ z
  · have := GlobalTheory.FixedAlgebraic.mem_of_forall_ringEquiv_fixed σ.fieldRange z ha (fun τ hτ => hz τ
      (fun x => hτ _ ⟨x, rfl⟩))
    simpa using this
  · obtain ⟨τ, hτ, hne⟩ := exists_ringEquiv_fix_ne K σ z ha
    exact absurd (hz τ hτ) hne

theorem span_conj_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι]
    (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) →
    Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  intro K _ _ σ ι _ e he
  classical
  let R : Submodule ℂ (ι → ℂ) :=
    { carrier := {z | ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0}
      add_mem' := by
        intro a b ha hb φ hφ
        simp only [Set.mem_setOf_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, ha φ hφ,
          hb φ hφ, add_zero]
      zero_mem' := by intro φ hφ; simp
      smul_mem' := by
        intro c a ha φ hφ
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          ha φ hφ, mul_zero] }
  have hRmem : ∀ z, z ∈ R ↔ ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0 :=
    fun z => Iff.rfl
  have key : ∀ n, ∀ z ∈ R, (Finset.univ.filter (fun i => z i ≠ 0)).card = n → z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z hz hcard
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    set z' := (z i0)⁻¹ • z with hz'
    have hz'R : z' ∈ R := R.smul_mem _ hz
    have hz'i0 : z' i0 = 1 := by simp [z', hi0]
    have hsupp : (Finset.univ.filter (fun i => z' i ≠ 0))
        = Finset.univ.filter (fun i => z i ≠ 0) := by
      ext i; simp [z', hi0]
    have hfix : ∀ ψ : ℂ ≃+* ℂ, (∀ x, ψ (σ x) = σ x) → ∀ i, ψ (z' i) = z' i := by
      intro ψ hψ
      have hw : (fun i => ψ (z' i)) - z' ∈ R := by
        refine R.sub_mem ?_ hz'R
        rw [hRmem]
        intro φ hφ
        have h1 := (hRmem z').1 hz'R (φ.trans ψ.symm) (by
          intro x
          rw [RingEquiv.trans_apply, hφ, RingEquiv.symm_apply_eq, hψ])
        have h2 := congrArg ψ h1
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_mul] using h2
      have hlt : (Finset.univ.filter (fun i => ((fun i => ψ (z' i)) - z') i ≠ 0)).card < n := by
        rw [← hcard, ← hsupp]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨i0, by simp [hz'i0], by simp [hz'i0]⟩
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq] at hi ⊢
          intro h
          apply hi
          simp [h]
      have h3 := ih _ hlt _ hw rfl
      intro i
      have h4 := congrFun h3 i
      simpa [sub_eq_zero] using h4
    choose c hc using fun i => exists_eq_of_forall_fixed K σ (z' i) (fun τ hτ => hfix τ hτ i)
    have hc0 := he c (by
      have h5 := (hRmem z').1 hz'R (RingEquiv.refl ℂ) (fun x => rfl)
      simpa [hc] using h5)
    have h6 : z' i0 = 0 := by rw [← hc i0, hc0]; simp
    rw [hz'i0] at h6
    exact one_ne_zero h6
  by_contra hS
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS) inferInstance
  let z : ι → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hzR : z ∈ R := by
    rw [hRmem]
    intro φ hφ
    have hmem : (fun i => φ (e i)) ∈ Submodule.span ℂ
        {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} :=
      Submodule.subset_span ⟨φ, hφ, rfl⟩
    have h7 : f (fun i => φ (e i)) = 0 := by
      have h8 := Submodule.mem_map_of_mem (f := f) hmem
      rw [hf, Submodule.mem_bot] at h8
      exact h8
    rw [LinearMap.pi_apply_eq_sum_univ] at h7
    simpa [z, smul_eq_mul, mul_comm] using h7
  have hz0 := key _ z hzR rfl
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  have : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hz0 i
  simp [this]

end GlobalTheory.ConjSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelTranslateSumEqClassicalShortSeries
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SingleDatum.ShortSum
open GlobalTheory.AdTh.ShortSeries


set_option maxHeartbeats 1000000 in
theorem thetaKO_transSum_eq_short_series : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r g q0 : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (hq : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x₀ : Frame X.Ψ r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsMod W hr X → IsSympl X bas → IsONFr X x₀ → IsInvOf W hr X x₀ s → IsBasOf W hr X hq x₀ BW → IsVarOf V W X q0 vr → ∀ (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l₂.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E, IsRoots l₂ (latR hr (latG W k)) mk N Y → ∀ (v : TF V.rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (latR hr (latG W k))) v → Reads θ V W hr X bas idx (om (1, k) f₀) (a • v) (frMove θ W hr X k x₀) → ∀ (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW (transSum ψ V W l₂ ι e f₀ w) (MvPolynomial.rename vr P)) = (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * (((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℂ)) * ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR hr (latG W k)) v w Y) P (frMove θ W hr X k x₀) := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP ι hι hrt l₂ e he r g q0 hr X hq bas idx x₀ vr BW hM hS hx hinv hbas hvr
    bad N h k Λ mk e' Ps y hbad he' hPs hh hsupp hdet hΛ htriv hlev hmk Y hY v a hv hR w P d hd
  choose p hp using fun q => exists_finOf V W hr (Y q)
  obtain ⟨hthP, hdat⟩ := _root_.GlobalTheory.AdTh.MovedSum.moved_transSum D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP
    ι hι l₂ e he r hr bad N h k Λ mk hbad ⟨hh, e', Ps, he', hPs, hsupp⟩ hΛ htriv hlev hmk Y (fun q => (p q).1)
    (fun q => (p q).2) hY hp w
  obtain ⟨hP, -, hV0, hW0, hVs, hWs, hVstd, -, hvac⟩ := hVP
  have hψ := hP.weil.std
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin V.rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin V 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even hr X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt _ k) * s τ * compAt θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (fin W k), w = a • v} →
      latR hr (latG W k) = latR hr L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := _root_.GlobalTheory.AdTh.SplitClass.om_reads_projA D _ _ _ _ _ _ _ hP _ g hr X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move hr X hinv k) _ hvac' _ hR e' Ps h y he' hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even hr X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl w (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hrd := (reads_linear_injective D _ _ _ _ _ g hr X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (w _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP hr X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ w Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rw [hpar]
  push_cast
  ring
end GlobalTheory.SingleDatum.ShortSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClass
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace CompanionTheory.Member.ThetaTranslation

theorem thetaKO_translate {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeilDatumO ψ S T χS χT om) (θ : InfFam D)
    (hθ : IsInfFam θ) (z : GA D S) (hz : z ∈ GfC S) (sS sT BS BT) (f : WO S T → ℂ) (P) (hf : IsThetaFunO ψ S T f)
    (c : ℂ) (h : GA D S) (g : GA D T) :
    thetaKO om h g (pureTensorO ψ θ S T sS sT BS BT (c • om (z, 1) f) P) =
      c * thetaKO om (h * z) g (pureTensorO ψ θ S T sS sT BS BT f P) := by
  rw [GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T χS χT om hom θ hθ z hz 1 (one_mem _) sS sT BS BT f P hf]
  unfold thetaKO
  have e : ((h * z, g) : GA D S × GA D T) = (h, g) * (z, 1) := by rw [Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, map_smul, Module.End.mul_apply, Pi.smul_apply, smul_eq_mul]

end CompanionTheory.Member.ThetaTranslation

set_option maxHeartbeats 1000000 in
theorem CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t z c hz u h w g
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h1 := hC.thP.pt_theta i t 1
    unfold RealDat.ptP at h1
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at h1
  exact CompanionTheory.Member.ThetaTranslation.thetaKO_translate R.ψ _ _ _ _ (R.ωP i t) (hC.thP.ωP i t) R.θ hC.models.inf z hz _ _ _ _ _ _ hf c h g

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
theorem _root_.GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | exact CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | (intros; apply CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class <;> assumption)

end
end

