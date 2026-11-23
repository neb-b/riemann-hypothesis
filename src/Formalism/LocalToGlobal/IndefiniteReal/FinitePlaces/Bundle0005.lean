module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
public import ReciprocityTheory.AdeleApproximation.AdeleIntA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology NumberField.InfinitePlace.Completion
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (a a' : Ainf F) (b b' : Af F) : pairA F (a + a') (b + b') = pairA F a b + pairA F a' b' := rfl

theorem pairA_split (a : Ainf F) (b : Af F) : pairA F a b = pairA F a 0 + pairA F 0 b := by
  rw [← pairA_add, add_zero, zero_add]

theorem algebraMap_AF (q : F) :
    algebraMap F (AF F) q = pairA F (algebraMap F (Ainf F) q) (algebraMap F (Af F) q) := rfl

theorem exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * n) = 1 := by
  rw [show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem exists_nsmul_mem_cpt {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  haveI : DiscreteTopology (X ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hSfin : ((fun y : X => (y : X ⧸ H)) '' K).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hord : ∀ y ∈ K, IsOfFinAddOrder (y : X ⧸ H) := by
    intro y hy
    obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => ((n • y : X) : X ⧸ H)) (fun n => Set.mem_image_of_mem _ (hKs y hy n)) hSfin
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨c + 1, Nat.succ_pos c, ?_⟩
    have h2 : (a + (c + 1)) • (y : X ⧸ H) = a • (y : X ⧸ H) := by
      rw [← Nat.add_assoc, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul]
      exact he.symm
    rw [add_nsmul] at h2
    simpa using h2
  refine ⟨∏ q ∈ hSfin.toFinset, addOrderOf q, ?_, ?_⟩
  · apply Finset.prod_pos
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hSfin.mem_toFinset.mp hq
    exact (hord y hy).addOrderOf_pos
  · intro y hy
    have hmem : (y : X ⧸ H) ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr ⟨y, hy, rfl⟩
    have h0 : (∏ q ∈ hSfin.toFinset, addOrderOf q) • (y : X ⧸ H) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem (fun q => addOrderOf q) hmem)
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h0
    exact h0

end Gen

section Psi

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem sum_fEmb (x : D.host.F) : ∑ τ : D.what₂.Tau, Eqv.fEmb D τ x = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  classical
  have hb : Function.Bijective (fun τ => Eqv.fEmb D τ) := by
    constructor
    · intro τ τ' h
      simp only at h
      have h' : Eqv.plW D τ = Eqv.plW D τ' := by
        show InfinitePlace.mk (Eqv.fEmb D τ) = InfinitePlace.mk (Eqv.fEmb D τ')
        rw [h]
      rw [Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl] at h'
      exact (Formalism.L2.Host.tauPl D).injective h'
    · intro φ
      refine ⟨(Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ), ?_⟩
      have h1 := Eqv.plW_embedding D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      rw [Eqv.plW_symm] at h1
      have hr := Eqv.fEmb_isReal D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      show Eqv.fEmb D _ = φ
      rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
      · rw [← h1, h2]
      · rw [← h1] at hr
        rw [← h1, h2]
        rw [h2] at hr
        exact ComplexEmbedding.isReal_conjugate_iff.mp hr
  have htr := trace_eq_sum_embeddings (K := ℚ) (L := D.host.F) (E := ℂ) (x := x)
  rw [show ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.F x) from
    (eq_ratCast _ _).symm, htr]
  let e : (D.host.F →+* ℂ) ≃ (D.host.F →ₐ[ℚ] ℂ) := RingHom.equivRatAlgHom D.host.F ℂ
  exact Fintype.sum_bijective (e ∘ fun τ => Eqv.fEmb D τ) (e.bijective.comp hb) _ _ (fun τ => rfl)

theorem psi_inf (hψ : IsStdChar D ψ (-1)) (a : Ainf D.host.F) :
    ψ (pairA D.host.F a 0) = Complex.exp (-(2 * Real.pi * Complex.I * ∑ τ, Eqv.gW D (Eqv.plW D τ) a)) := by
  obtain ⟨-, -, hθ⟩ := hψ
  have h := hθ (Eqv.thetaC D) (Eqv.isInfFam_thetaC D) a
  simp only [Eqv.thetaC_tmul, map_one, mul_one] at h
  rw [show ψ (pairA D.host.F a 0) = psiInf D.host.F ψ a from rfl, h]
  congr 1
  push_cast
  ring

theorem psi_fin_rat (hψ : IsStdChar D ψ (-1)) (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ D.host.F q : ℚ)) := by
  have hrat : ψ (algebraMap D.host.F (AF D.host.F) q) = 1 := by
    obtain ⟨⟨-, -, h, -⟩, -⟩ := hψ
    exact h q
  have hinf := psi_inf hψ (algebraMap D.host.F (Ainf D.host.F) q)
  simp only [Eqv.gW_algebraMap, sum_fEmb] at hinf
  rw [algebraMap_AF, pairA_split, AddChar.map_add_eq_mul, hinf] at hrat
  have h2 := congrArg
    (fun w => Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F q : ℚ) : ℂ)) * w) hrat
  simp only [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul, mul_one] at h2
  exact h2

theorem psi_pair0_add (a b : Af D.host.F) :
    ψ (pairA D.host.F 0 (a + b)) = ψ (pairA D.host.F 0 a) * ψ (pairA D.host.F 0 b) := by
  rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]

theorem psi_invDiff (hψ : IsStdChar D ψ (-1)) (d : D.host.F) (hd : d ∈ invDiff D.host.F) (y : Af D.host.F)
    (hy : y ∈ intAf D.host.F) : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * y)) = 1 := by
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  let md : Af D.host.F →+ Af D.host.F := AddMonoidHom.mulLeft (algebraMap D.host.F (Af D.host.F) d)
  let H : AddSubgroup (Af D.host.F) := AddSubgroup.comap md G
  have hHo : IsOpen (H : Set (Af D.host.F)) := hGo.preimage (continuous_const.mul continuous_id)
  obtain ⟨m, hm, hmH⟩ := exists_nsmul_mem_cpt (Formalism.IndefR.PHeisFC.Ohat D.host.F)
    (Formalism.IndefR.PHeisFC.isCompact_Ohat D.host.F)
    (fun y hy n => (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F).toAddSubgroup.nsmul_mem hy n) H hHo
  have hm0 : ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨a, ha⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx y (fun v => hy v) _ hm0

  set z : Af D.host.F := algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
    (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F)) with hz
  have hmF : (m : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hyz : y = algebraMap D.host.F (Af D.host.F) (a : D.host.F) + m • z := by
    rw [hz, nsmul_eq_mul, ← mul_assoc, show (m : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (m : D.host.F) by
      simp, ← map_mul, mul_one_div_cancel hmF, map_one, one_mul]
    abel
  have hzint : z ∈ Formalism.IndefR.PHeisFC.Ohat D.host.F := by
    intro v
    have hv := ha v
    show (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
      (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v ∈ v.adicCompletionIntegers D.host.F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
        (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v =
        algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F)) *
          (y v - algebraMap D.host.F _ (algebraMap (𝓞 D.host.F) D.host.F a)) := rfl
    rw [e, map_mul]
    have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F))) =
        (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ := by
      rw [one_div, map_inv₀, map_inv₀]
      congr 1
      rw [show ((m : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((m : ℕ) : 𝓞 D.host.F) by simp]
      exact ReciprocityTheory.UG.AdeleIntA.val_R v _
    rw [hval]
    have hv0 : v.intValuation ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := v.intValuation_ne_zero _ hm0
    calc (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * Valued.v _
        ≤ (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * v.intValuation ((m : ℕ) : 𝓞 D.host.F) :=
          mul_le_mul' le_rfl hv
      _ = 1 := inv_mul_cancel₀ hv0
  rw [hyz, mul_add, psi_pair0_add]
  have h1 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d *
      algebraMap D.host.F (Af D.host.F) (a : D.host.F))) = 1 := by
    rw [← map_mul, psi_fin_rat hψ]
    obtain ⟨n, hn⟩ := hd a
    rw [hn]; push_cast; exact exp_two_pi_int n
  have h2 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * m • z)) = 1 :=
    hG _ (hmH z hzint)
  rw [h1, h2, one_mul]

end Psi

section Kernel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isInt_of_intAf (y : Af D.host.F) (hy : y ∈ intAf D.host.F) : ReciprocityTheory.UG.AdeleIntA.IsInt y := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

theorem intAf_of_isInt (y : Af D.host.F) (hy : ReciprocityTheory.UG.AdeleIntA.IsInt y) : y ∈ intAf D.host.F := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

theorem intAf_mul {x y : Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) : x * y ∈ intAf D.host.F := by
  exact intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_mul (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))

theorem intAf_int (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  have h := ReciprocityTheory.UG.AdeleIntA.isInt_R (K := D.host.F) r
  rw [IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F] at h
  exact intAf_of_isInt _ h

theorem one_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  simpa using intAf_int (D := D) 1

end Kernel

section Exist

variable {D : D7}

end Exist

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.HeisSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate ContDiff

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem trace_fst_eq_zero (z : AE D) (hz : infPart D z = 0) :
    fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, fstA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).1 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_fst]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

theorem trace_snd_eq_zero (z : AE D) (hz : finPart D z = 0) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) = 0 := by
  have hc : ∀ k, sndA D.host.F (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k) = 0 := fun k => by
    show (Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k).2 = 0
    rw [← Formalism.IndefR.PHeisTh.repr_snd]
    have : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z = 0 := hz
    rw [this, map_zero]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).sum_repr z, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  have : (Formalism.IndefR.PHeisFC.bA D.host.F D.host.E).repr z k = Formalism.IndefR.PHeisFC.cE D.host.F D.host.E z k := rfl
  rw [this, hc, zero_mul]

variable (S T : HSp D)

set_option synthInstance.maxHeartbeats 400000 in
theorem infPart_hO (u w : MO S T) (hu : u.map (infPart D) = 0) : infPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, infPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum (infPart D), map_mul (infPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_hO (u w : MO S T) (hu : u.map (finPart D) = 0) : finPart D (hO S T u w) = 0 := by
  have h0 : ∀ d a, finPart D (u d a) = 0 := fun d a => congrFun (congrFun hu d) a
  unfold hO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum (finPart D), map_mul (finPart D), h0, mul_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_fst_eq_zero (u w : MO S T) (hu : u.map (infPart D) = 0) : fstA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_fst_eq_zero _ ?_
  rw [map_mul (infPart D), infPart_hO S T u w hu, mul_zero]

set_option synthInstance.maxHeartbeats 200000 in
theorem symplO_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplO S T u w) = 0 := by
  unfold symplO
  refine trace_snd_eq_zero _ ?_
  rw [map_mul (finPart D), finPart_hO S T u w hu, mul_zero]

theorem symplOH_snd_eq_zero (u w : MO S T) (hu : u.map (finPart D) = 0) : sndA D.host.F (symplOH S T u w) = 0 := by
  unfold symplOH
  rw [map_mul, symplO_snd_eq_zero S T u w hu, mul_zero]

def sndSympl (w : MO S T) : MO S T →+ Af D.host.F where
  toFun u := sndA D.host.F (symplO S T u w)
  map_zero' := by rw [symplO_zero_left, map_zero]
  map_add' u u' := by rw [symplO_add_left, map_add (f := _)]

theorem heisStable : HeisStable D := by
  intro ψ hψ S T w f hf
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  obtain ⟨U, hUo, hU⟩ := hf.level
  let H : AddSubgroup (WO S T) := AddSubgroup.comap (sndSympl S T w) G
  have hHo : IsOpen (H : Set (WO S T)) :=
    hGo.preimage (continuous_snd.comp (cont_symplO_left S T w))
  refine ⟨fun γ z => ?_, ⟨U ⊓ H, ?_, fun u hu h0 => ?_⟩, cont_heis S T hψ hf w, fun k L hL hL0 x => ?_⟩
  ·
    unfold heisO
    rw [show ratW T S γ + z + w = ratW T S γ + (z + w) by abel, hf.quasi γ (z + w), ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    have key : symplOH S T (ratW T S γ + z) w + -symplOH S T (ratW T S γ) (z + w) =
        -symplOH S T (ratW T S γ) z + symplOH S T z w := by
      rw [symplOH_add_left, symplOH_add_right]; ring
    rw [key]
  · rw [AddSubgroup.coe_inf]; exact hUo.inter hHo
  ·
    have hfu := hU u hu.1 h0
    have hc : ψ (symplO S T u w) = 1 := by
      have e : symplO S T u w = pairA D.host.F 0 (sndA D.host.F (symplO S T u w)) := by
        refine Prod.ext ?_ rfl
        exact symplO_fst_eq_zero S T u w h0
      rw [e]; exact hG _ hu.2
    funext z
    have k1 := congrFun hfu (z + w)
    unfold heisO at k1 ⊢
    have hfz : f (z + w + u) = ψ (-(symplOH S T (z + w) u)) * f (z + w) := by
      rw [AddChar.map_neg_eq_inv, ← k1]; field_simp [psi_ne hψ]
    rw [show z + u + w = z + w + u by abel, hfz, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    have key : symplOH S T z u + symplOH S T (z + u) w + -symplOH S T (z + w) u =
        symplOH S T z w + symplO S T u w := by
      rw [symplOH_add_left, symplOH_add_left, symplOH_swap S T u w, ← symplOH_two]; ring
    rw [key, AddChar.map_add_eq_mul, hc, mul_one]
  ·
    let s : (Fin k → ℝ) →+ Ainf D.host.F :=
      { toFun := fun t => fstA D.host.F (symplOH S T (L t) w)
        map_zero' := by simp only [map_zero]; unfold symplOH; rw [symplO_zero_left, mul_zero, map_zero]
        map_add' := fun t t' => by simp only [map_add (f := _)]; rw [symplOH_add_left, map_add (f := _)] }
    have hs : Continuous s := continuous_fst.comp ((cont_symplOH_left S T w).comp hL)
    have e : (fun t => heisO ψ S T w f (x + L t)) =
        fun t => ψ (symplOH S T x w) * ψ (pairA D.host.F (s t) 0) * f (x + w + L t) := by
      funext t
      unfold heisO
      have ep : symplOH S T (L t) w = pairA D.host.F (s t) 0 :=
        Prod.ext rfl (symplOH_snd_eq_zero S T (L t) w (hL0 t))
      rw [symplOH_add_left, AddChar.map_add_eq_mul, ep, show x + L t + w = x + w + L t by abel]
    rw [e]
    exact (contDiff_const.mul (Formalism.IndefR.PHeisTh.psiSmooth D ψ hψ k s hs)).mul (hf.smooth k L hL hL0 (x + w))

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
section
noncomputable section

namespace Formalism.IndefR.Fin.Lifts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped ComplexOrder
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    unfold Formalism.UG.Jpq
    rw [show (-1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 by ext i; exact i.elim0, Matrix.fromBlocks_one]
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.star_apply]
  rw [hJ, hc] at hP
  have hU : IsUnit (P : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := P.isUnit
  have h1 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU).1 (hP ▸ Matrix.PosDef.one)
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j
    simp
  rw [hG]
  exact h1.submatrix e.injective

end Formalism.IndefR.Fin.Lifts

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SecondCharacterFact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Places

variable {F : Type} [Field F] [NumberField F]

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  have h2 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv
  have hv1 : v.valuation F x ≤ 1 := not_lt.1 hv.1
  have hv2 : v.valuation F x⁻¹ ≤ 1 := not_lt.1 hv.2
  have hpos : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have hval : v.valuation F x = 1 := by
    rw [map_inv₀, inv_le_one₀ hpos] at hv2
    exact le_antisymm hv1 hv2
  have h := NumberField.FinitePlace.norm_embedding' (K := F) v x
  rw [hval] at h
  simp only [map_one, NNReal.coe_one] at h
  exact h

end Places

section Main

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)



end Main

variable {D : D7}

end Formalism.IndefR.Fin.U1

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnrOff (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (e + cA D e) * (x : AE D) = e + cA D e → χ x = 1




end Formalism.IndefR.Fin

end
end

