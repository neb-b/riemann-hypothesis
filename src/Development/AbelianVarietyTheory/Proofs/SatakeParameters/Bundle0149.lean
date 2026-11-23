module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLattice
section
namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem latA_single_mem {ι : Type} [DecidableEq ι] (j i : ι) : (Pi.single j (1 : L) : ι → L) i ∈ Formalism.UG.intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem latA_dot_mem {ι : Type} [Fintype ι] {u w : ι → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : u ⬝ᵥ w ∈ Formalism.UG.intL L :=
  sum_mem fun i _ => mul_mem (hu i) (hw i)

theorem latA_sum {n m : ℕ} (c : Matrix (Fin n) (Fin n) L) (hc : c.det ≠ 0) (y : Matrix (Fin n) (Fin m) L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.Hk3.HoweG.exists_square_span_cols L n (Fin n ⊕ Fin m) (Matrix.fromCols c y)
  have key : ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
    intro v
    rw [← hb v]
    constructor
    · rintro ⟨u, w, hu, hw, rfl⟩
      refine ⟨Sum.elim u w, ?_, ?_⟩
      · rintro (i | i)
        · exact hu i
        · exact hw i
      · rw [Matrix.fromCols_mulVec_sumElim]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u ∘ Sum.inl, u ∘ Sum.inr, fun i => hu _, fun i => hu _, ?_⟩
      rw [← Matrix.fromCols_mulVec_sumElim, Sum.elim_comp_inl_inr]
  have hcol : ∀ j : Fin n, ∃ t : Fin n → L, c *ᵥ Pi.single j 1 = b *ᵥ t := by
    intro j
    obtain ⟨t, -, ht⟩ := (key (c *ᵥ Pi.single j 1)).1
      ⟨Pi.single j 1, 0, latA_single_mem j, fun _ => zero_mem _, by simp⟩
    exact ⟨t, ht⟩
  choose t ht using hcol
  have hT : b * (Matrix.of t)ᵀ = c := by
    ext i j
    have := congrFun (ht j) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    rfl
  have hdet : b.det ≠ 0 := by
    intro h
    apply hc
    rw [← hT, Matrix.det_mul, h, zero_mul]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero b hdet, key⟩

theorem latA_basis (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ)
    (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := latA_sum (1 : Matrix (Fin n) (Fin n) L) (by simp) xᵀ
  have hN : ∀ u : Fin n → L, ((∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L)) ↔
      ∀ j, ((b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u) j ∈ Formalism.UG.intL L := by
    intro u
    have dual : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) L) (t : Fin k → L), (M *ᵥ t) ⬝ᵥ u = t ⬝ᵥ (Mᵀ *ᵥ u) := by
      intro k M t
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    constructor
    · rintro ⟨h1, h2⟩ j
      obtain ⟨l, w, hl, hw, e⟩ := (hb ((b : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1)).2
        ⟨_, latA_single_mem j, rfl⟩
      have e2 := dual (b : Matrix (Fin n) (Fin n) L) (Pi.single j 1)
      rw [single_one_dotProduct, e, add_dotProduct, dual xᵀ, Matrix.one_mulVec, Matrix.transpose_transpose] at e2
      rw [← e2]
      exact add_mem (latA_dot_mem hl h1) (latA_dot_mem hw h2)
    · intro h
      refine ⟨fun i => ?_, fun k => ?_⟩
      · obtain ⟨t, ht, e⟩ := (hb (Pi.single i 1)).1
          ⟨Pi.single i 1, 0, latA_single_mem i, fun _ => zero_mem _, by
            rw [Matrix.one_mulVec, Matrix.mulVec_zero, add_zero]⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
      · obtain ⟨t, ht, e⟩ := (hb (xᵀ *ᵥ Pi.single k 1)).1
          ⟨0, Pi.single k 1, fun _ => zero_mem _, latA_single_mem k, by simp⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, dual xᵀ, Matrix.transpose_transpose, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
  have hmul : (b : Matrix (Fin n) (Fin n) L)ᵀ * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hmul' : ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (b : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hdet : (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨a, ha⟩ := latA_sum _ hdet y
  refine ⟨a, fun v => ?_⟩
  rw [← ha v]
  constructor
  · rintro ⟨u, w, h1, h2, hw, rfl⟩
    refine ⟨(b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u, w, (hN u).1 ⟨h1, h2⟩, hw, ?_⟩
    rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
  · rintro ⟨u, w, hu, hw, rfl⟩
    have := (hN (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u)).2 (by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]; exact hu)
    exact ⟨_, w, this.1, this.2, hw, rfl⟩

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
section
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLat
variable {D : D7}

theorem under_eq_of_delta {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {P : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0) : P.under (𝓞 D.host.F) = v := by
  by_contra hne
  exact h1 ((GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P hne)

theorem place_of_primeIdem {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε ∧ P.under (𝓞 D.host.F) = v := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 P e f h).1
  rcases h with ⟨hid, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, hT⟩
  · obtain ⟨h1, h2, v, ε, hε, hsum⟩ := hid.1
    refine ⟨v, ε, hε, hsum, under_eq_of_delta hΦ hε ?_⟩
    have hinf : infPart D e = 0 := by
      have : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
      rw [this, map_mul, hsum, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, mul_zero]
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ h1 hinf P).1 hid.2
    have hc0 : Φ (cA D e) P = 0 := by
      have := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
      rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul] at this
      exact this.symm
    rw [← hsum, GlobalTheory.IdemSupport.ev_add, hd.2.1, hc0, add_zero]
    exact one_ne_zero
  · refine ⟨v, ε, hε, rfl, under_eq_of_delta hΦ hε ?_⟩
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hff (GlobalTheory.IdemSupport.place_comp hΦ hε).1 P).1 hT
    rw [hd.2.1]; exact one_ne_zero
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem two_not_mem {P : Pl D.host.E} {e : AE D} (he : GlobalTheory.IdemSupport.Comparison₂ P e) (hc : cA D e = e) (hi : e * e = e)
    (h0 : infPart D e = 0) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hi h0 P).1 he
  have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
  rw [hc] at hd'
  have hPP : GlobalTheory.IdemSupport.cP P = P := by
    by_contra hne
    have := hd.2.2 _ hne
    rw [hd'.2.1] at this
    exact one_ne_zero this
  intro h2
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [GlobalTheory.IdemSupport.cO_coe, GlobalTheory.SplitIdem.star_eq_conj]
    rfl
  rw [this, ← GlobalTheory.IdemSupport.mem_cP, hPP]

theorem unit_factor {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (M : ℕ)
    (hM : (M : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ γ ∈ intAf D.host.F, ε = pairA D.host.F 0 ((M : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hM
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (M : D.host.F) = 1 := by
        rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hM
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  · congr 1
    rw [← mul_assoc, mul_comm _ α, mul_assoc, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) M,
      ← map_mul, mul_inv_cancel₀ hM0, map_one, mul_one]
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem intAf_mul {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) :
    x * y ∈ intAf D.host.F := fun w => by
  rw [map_mul]; exact mul_mem (hx w) (hy w)

theorem pairA_mul (x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 x * pairA D.host.F 0 y = pairA D.host.F 0 (x * y) := by
  exact Prod.ext (zero_mul _) rfl

theorem pairA_smul (a : D.host.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 (algebraMap D.host.F _ a * x) = a • pairA D.host.F 0 x := by
  refine Prod.ext ?_ ?_
  · exact (smul_zero a).symm
  · exact (Algebra.smul_def a x).symm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lat_scale (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (NS NT c : ℕ)
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ ΛS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ ΛT)
    (γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hγ : γ ∈ intAf D.host.F) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True) :
    ∃ u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) * u i j =
        (c • u') i j := by
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  let ψc : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) c
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)).map ψc).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨Matrix.of fun i j => (pairA D.host.F 0 (γ * α)) ⊗ₜ[D.host.F]
        (a * ((NT : D.host.E) • t) i * ∑ k, star (((NS : D.host.E) • s) k) * S.gram k j),
      AddSubgroup.subset_closure ⟨γ * α, intAf_mul hγ hα, fun v hv => (hv trivial).elim, a, ha, _, hS s hs, _, hT t ht, rfl⟩, ?_⟩
    ext i j
    simp only [ψc, φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.smul_apply]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, pairA_mul, mul_assoc (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) γ α, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)),
      pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
    congr 1
    rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
    simp only [star_mul', star_natCast, Nat.cast_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨u', hu', he⟩ := key hu
  exact ⟨u', hu', fun i j => (congrFun (congrFun he i) j).symm⟩
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat

theorem isVacAt_of_isLatVac : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  intro D ψ S T βS βT ΛS ΛT NS NT hS hT P hP f₀ hth hvac
  refine ⟨hth, fun e f' he u hu hhalf => ?_⟩
  have hNS : (NS : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_right _ h)
  have hNT : (NT : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_left _ h)
  obtain ⟨v, ε, hε, hf, hv⟩ := place_of_primeIdem he
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e f' he).1
  have hunder : ∀ c : ℕ, (c : 𝓞 D.host.E) ∉ P.asIdeal → ((c * NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro c hc h
    rw [← hv] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact hc h
      · exact hNS h
    · exact hNT h
  rcases he with ⟨hid, rfl⟩ | ⟨hfe, -, hTie⟩
  · have hfu : ∀ i j, (e + cA D e) * u i j = u i j := by
      have h1 := hid.1.1
      have h2 := hid.1.2.1
      have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
      have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
      rcases hhalf with h | h <;> intro i j
      · have h' : e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
      · have h' : cA D e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (1 * NS * NT) (hunder 1 (by rw [Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)))
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 1 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = u' := by
      ext i j
      rw [← hfu i j, hf, hεγ, heq, one_smul]
    subst hue
    rcases hhalf with h | h
    · exact hvac.2 e hid.1 u hu' h
    · refine hvac.2 (cA D e) ⟨by rw [← map_mul, hid.1.1], by rw [cA_cA, mul_comm]; exact hid.1.2.1, ?_⟩ u hu' h
      obtain ⟨w, η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w, η, hη, by rw [cA_cA, add_comm]; exact hwη⟩
  · have hf' : e = algebraMap (AF D.host.F) (AE D) ε := hfe.symm.trans hf
    have hc : cA D e = e := by rw [hf']; exact GlobalTheory.IdemSupport.cA_algebraMap ε
    have hi : e * e = e := hfe ▸ hff
    have h0 : infPart D e = 0 := by
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
      rw [hf']; exact (GlobalTheory.IdemSupport.place_comp hΦ hε).1
    have h2 := two_not_mem hTie hc hi h0
    have hfu : ∀ i j, e * u i j = u i j := by
      rcases hhalf with h | h
      · exact fun i j => h i j
      · rw [hc] at h; exact fun i j => h i j
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (2 * NS * NT) (hunder 2 h2)
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 2 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = 2 • u' := by
      ext i j
      rw [← hfu i j, hf', hεγ, heq]
    rw [hue]
    exact hvac.1 u' hu'

end GlobalTheory.VacLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEq
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverse
section
open Matrix

namespace GlobalTheory.Hk3

theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add (f := _), map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add (f := _), map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
end

