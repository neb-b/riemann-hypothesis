module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsFin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsES
section
noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsES

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsFin
  Formalism.L2.SG.Pf.AllRowsRhoX

variable {D : D7}

abbrev CV (D : D7) : Type := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)

def Ea (a : CV D) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun γ : G0g D.nd =>
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)

theorem Ea_coeff (a : CV D) (γ : G0g D.nd) :
    (Ea a).coeff γ = haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) := by
  simp [Ea, MonoidAlgebra.coeff_ofCoeff]

open Classical in
theorem ES_eq (S : Set (Tup2 D)) : ES S = ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a := by
  apply MonoidAlgebra.ext
  ext γ
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_filter]
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Ea_coeff]
  · rfl

theorem monicOf_inj {g : ℕ} [Fact g.Prime] {N : ℕ} {a b : Fin N → ZMod g}
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  rw [← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf a i, ← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf b i, h]

open Classical in
theorem Ea_mul (a b : CV D) : Ea a * Ea b = if a = b then Ea a else 0 := by
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ea_coeff]
  have key : ∑ δ : G0g D.nd, (∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (δ kv)) *
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))).coeff ((δ⁻¹ * γ) kv) =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) *
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv)))).coeff (γ kv) := by
    simp only [coeff_mul_fin]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [key]
  split_ifs with hab
  · subst hab
    rw [Ea_coeff]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [D.ntypes.eSer_idem]
  · obtain ⟨kv, hkv⟩ : ∃ kv, a kv ≠ b kv := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have h0 : (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) * (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) = 0 :=
      D.ntypes.eSer_orth kv.1 _ _ fun h => hkv (monicOf_inj h)
    rw [Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; simp)]
    simp


open Classical in
theorem ES_idem (S : Set (Tup2 D)) : ES S * ES S = ES S := by
  rw [ES_eq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Ea_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd ha h), if_pos rfl]

theorem ES_central (S : Set (Tup2 D)) (y : MonoidAlgebra ℂ (G0g D.nd)) : ES S * y = y * ES S :=
  central_of_class _ (ES_conj S) y

theorem ES_selfadj (S : Set (Tup2 D)) : conjA (ES S) = ES S :=
  selfadj_of_central_idem _ (ES_idem S) (ES_central S)

end Formalism.L2.SG.Pf.AllRowsES
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ContinuousAdjugate
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

section Pack

variable {n : ℕ} (ε : Fin n → Bool)

def mkUJ (y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨y, Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε,
    mul_eq_one_comm.1 (by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]),
    by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]⟩, hy⟩

end Pack

section Adj

variable {m : ℕ}

end Adj

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharN
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D) {kv : Σ k : Fin 2, D.nd.PlG k}

theorem level_mem_wB' (kv : Σ k : Fin 2, D.nd.PlG k) : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal :=
  g_mem_of_gk X (gk_mem X kv)

theorem psiK_ne {ε : 𝓞 X.B.I.E} (hε1 : ε - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) : psiK X ε hε ≠ 1 := by
  intro h1
  have hp := D.host.g_prime kv.1
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩

  have hm : ∀ m : ℕ, X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) = 1 := by
    intro m
    have h2 := congrArg (fun ψ : AddChar (ZMod (D.host.g kv.1)) ℂ => ψ (m : ZMod (D.host.g kv.1))) h1
    simp only [psiK_apply, AddChar.one_apply, ZMod.val_natCast] at h2
    rw [← psi_period X hε (m % D.host.g kv.1) (m / D.host.g kv.1), Nat.mod_add_div] at h2
    exact h2

  have hb : ∀ b : 𝓞 X.B.I.F, X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b : 𝓞 X.B.I.E) : X.B.I.E)))) = 1 := by
    intro b
    set bE : 𝓞 X.B.I.E := algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b
    obtain ⟨c, hc⟩ := int_surj X.B.I (wK X kv) hp (card_wK X kv) (Ideal.Quotient.mk _ bE)
    set m : ℕ := ((c : ZMod (D.host.g kv.1)).val : ℕ)
    have hbm : bE - (m : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
      have h1' : bE - (c : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
      have h2' : ((c : 𝓞 X.B.I.E) - (m : 𝓞 X.B.I.E)) ∈ (wK X kv).asIdeal := by
        have : ((c - (m : ℤ) : ℤ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
          rw [int_mem_iff X.B.I (wK X kv) hp (card_wK X kv), ← ZMod.intCast_eq_intCast_iff_dvd_sub]
          simp [m]
        simpa using this
      have := add_mem h1' h2'
      simpa using this
    have hall : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal →
        ε * (bE - (m : 𝓞 X.B.I.E)) ∈ P.asIdeal := by
      intro P hP
      by_cases hPw : P = wK X kv
      · rw [hPw]; exact Ideal.mul_mem_left _ _ hbm
      · exact Ideal.mul_mem_right _ _ (hεP P hP hPw)
    obtain ⟨c', hc'⟩ := mem_g_of_all X hall
    have e : iE X.B.I (ε * bE) = iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * iE X.B.I c' := by
      have : ε * bE = ε * (m : 𝓞 X.B.I.E) + ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c' := by rw [← hc']; ring
      rw [this]; simp [iE]
    have h3 := hm m
    rw [← psi_modg X _ (iE_int X.B.I c'), ← e] at h3
    have e2 : iE X.B.I (ε * bE) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((ε : X.B.I.E) * (bE : X.B.I.E)) := by
      simp [iE]
    rw [e2, divN_incl] at h3
    exact h3

  set τ := PI.ScPsiExists.UnitaryGroupMassFormula.tau X.B.I.cm.fixed
  set y : X.B.I.F := (((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E)
  have htr : ∀ z : 𝓞 X.B.I.F, ∃ n : ℤ, Algebra.trace ℚ X.B.I.F (y * algebraMap (𝓞 X.B.I.F) X.B.I.F z) = n := by
    intro z
    have h4 := X.psiEf_rat (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) *
      ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E)))
    rw [hb z, one_mul] at h4
    obtain ⟨n, hn⟩ := PsiCondAllPf.trace_of_psi X.B.I _ h4
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    have hz : ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z) := rfl
    have e3 : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z)) =
        (((X.B.g : ℕ) : X.B.I.F)⁻¹ * algebraMap (𝓞 X.B.I.F) X.B.I.F z) • (ε : X.B.I.E) := by
      rw [Algebra.smul_def, map_mul, map_inv₀, map_natCast]; ring
    rw [hz, e3, LinearMap.map_smul, smul_eq_mul]
    ring

  let v : HeightOneSpectrum (𝓞 X.B.I.F) :=
    { asIdeal := (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have h5 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) := by
          rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
        rw [hbot] at h5
        exact (by exact_mod_cast hp.ne_zero : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ≠ 0) ((Submodule.mem_bot _).1 h5) }
  have hv : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
    exact PsiCondAllPf.unram_of (D.host.g kv.1) hp v hv
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split kv.1) v hv).1
  obtain ⟨d, hd, hdv⟩ := PsiCondAllPf.exists_diff_not_mem v hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int y htr d hd
  obtain ⟨t, ht⟩ := PI.ScPsiExists.UnitaryGroupMassFormula.tau_int X.B.I.cm.fixed ε

  have hgc : ((X.B.g : ℕ) : 𝓞 X.B.I.F) * c = t * d := by
    apply FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) X.B.I.F
    have hg0 : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
    rw [map_mul, map_mul, hc, ht, map_natCast]
    show (X.B.g : X.B.I.F) * ((((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E) * _) = τ (algebraMap (𝓞 X.B.I.E) X.B.I.E ε) * _
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
  have htd : t * d ∈ v.asIdeal := by
    rw [← hgc]
    refine Ideal.mul_mem_right _ _ ?_
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact g_mem_of_gk X (gk_mem X kv)
  have htv : t ∈ v.asIdeal := (v.isPrime.mem_or_mem htd).resolve_right hdv

  have htw : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t ∈ (wK X kv).asIdeal := htv
  have hte : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t = ε + sigO X.B.I ε := by
    apply RingOfIntegers.ext
    show algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F t) = (ε : X.B.I.E) + star (ε : X.B.I.E)
    rw [ht, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply]
  have hsig : sigO X.B.I ε ∈ (wK X kv).asIdeal := by
    have : ε ∈ (wc X.B.I (wK X kv)).asIdeal :=
      hεP _ (natCast_mem_wc X.B.I (level_mem_wB' X kv)) (wK_ne_wc X kv kv).symm
    rwa [mem_wc] at this
  rw [hte] at htw
  have h1w : (1 : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
    have := sub_mem (sub_mem htw hε1) hsig
    convert this using 1; ring
  exact (wK X kv).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1w)

end Formalism.L2.SG.Pf.KppChar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP
section
noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.RMeasP

theorem rset_matGroup {k r : ℕ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : IsUnit g₀.det) :
    PI.IsMatGroup (Formalism.MainNotions.S.Rset k r g₀) := by
  have hui : IsUnit (g₀⁻¹).det := Matrix.isUnit_nonsing_inv_det g₀ hu
  have hc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hui
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset k r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_ofPred_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hset]
  exact ⟨hc.closed, hc.one_mem, hc.mul_mem, fun a ha => ⟨hc.inv_mem a ha, Matrix.mul_nonsing_inv a (hc.unit a ha)⟩⟩

theorem isHaarOn_smul' {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.MainNotions.S.IsHaarOn S μ) {c : ℝ≥0∞} (h0 : c ≠ 0) (h1 : c ≠ ⊤) : Formalism.MainNotions.S.IsHaarOn S (c • μ) := by
  unfold Formalism.MainNotions.S.IsHaarOn at h ⊢
  obtain ⟨hs, hne, hnull, hinv⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · first
      | infer_instance
      | (rw [← ENNReal.coe_toNNReal h1, ← ENNReal.smul_def]; infer_instance)
  · first
      | exact smul_ne_zero h0 hne
      | (intro hz
         apply hne
         have hu := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) hz
         simp [h0] at hu
         first
           | exact hu
           | exact Measure.measure_univ_eq_zero.mp hu)
  · rw [Measure.smul_apply, hnull, smul_zero]
  · intro s hs'
    rw [Measure.map_smul, hinv s hs']
    exact (Formalism.L2.SG.Pf.WFL.measurable_lmulM s).aemeasurable

theorem rMeas_exact (D : D7) (W : LocW D.R.k D.R.rS) (hz : inWb D.R.k D.R.rS W.z) (hT : 0 < Tz D.R.k D.R.rS W.z)
    (hz' : inWb D.R.k D.R.rS W.z') (hT' : 0 < Tz D.R.k D.R.rS W.z')
    (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG) (p : Point ℂ (D.R.rS + 1)) (g₀ : MatKR D.R.k D.R.rS)
    (hg : g₀ ∈ UH (Hpk D.R.k D.R.rS)) (hZ : Formalism.MainNotions.S.ZhatO D.R.k D.R.rS W.z W.z' g₀ = ptMat p) :
    ∃ ν, RMeas D W g₀ 1 ν := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨μ₀', c, hH, hc0, hc1, hmap⟩ :=
    Formalism.L2.SG.Pf.RootHaarLoc.locRootHaar D.R.k D.R.rS hk W.z W.z' hz hT hz' hT' p g₀ hg hZ
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) with hK
  have hu : IsUnit g₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).unit g₀ hg
  by_cases hK0 : K = 0
  ·

    exfalso
    have hka : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
      have h1 : 0 < D.host.ka := by
        unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
        have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
          abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
        have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
        positivity
      have h2 : 0 < gg D := by
        unfold gg
        have a := (D.host.g_prime 0).pos
        have b := (D.host.g_prime 1).pos
        positivity
      positivity
    rw [hK, ENNReal.ofReal_eq_zero] at hK0
    exact absurd hK0 (not_le.2 (pow_pos hka _))
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  set μ₀ : Measure (Mt D.R.k D.R.rS) := (K * c⁻¹) • μ₀' with hμ₀
  have hKc0 : K * c⁻¹ ≠ 0 := mul_ne_zero hK0 (ENNReal.inv_ne_zero.2 hc1)
  have hKc1 : K * c⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hKt (ENNReal.inv_ne_top.2 hc0)
  have hH0 : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀) μ₀ := isHaarOn_smul' hH hKc0 hKc1
  have hmap0 : μ₀.map (rootCoords D.R.k D.R.rS W.z' p) = K • volume := by
    rw [hμ₀, Measure.map_smul, hmap, smul_smul, mul_assoc, ENNReal.inv_mul_cancel hc0 hc1, mul_one]
    apply Continuous.aemeasurable
    unfold Formalism.MainNotions.S.rootCoords
    refine continuous_pi (fun q => ?_)
    unfold flagMat
    by_cases hi : q.1.1.val < D.R.rS
    · simp only [hi, ↓reduceDIte]
      fun_prop
    · simp only [hi, ↓reduceDIte]
      exact continuous_const
  have hid : μ₀.map (fun x => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = μ₀ := by
    have : (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
      funext x i j
      simp
    rw [this, Measure.map_id]
  have hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Nset D.R.k D.R.rS := (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem
  have hsub : Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀ ⊆ UH (Hpk D.R.k D.R.rS) := fun x hx => hx.1.1
  obtain ⟨ν, hν⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotM_exists (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group D.R.k D.R.rS)
    (rset_matGroup hu) hsub hG hH0
  refine ⟨ν, p, μ₀, ⟨1, hN1, 1, hN1, g₀, by simp, hZ, μ₀, hH0.2.2.1, ?_, hid.symm⟩, ?_⟩
  · rw [hmap0]
  · rw [ENNReal.ofReal_one, one_smul]
    exact hν

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

theorem rMeasExP_of_goodW (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) : Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C := by
  intro w _ hrep τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  exact rMeas_exact D (locW C u u' τ) h3 (by rw [h5]; exact hTu) h4 (by rw [h6]; exact hTu') h7
    (ptLoc D τ w) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)
    (Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _)
    (Formalism.L2.SG.Pf.RelPtR.zhatO_gamP C u u' w hrep τ)

end Formalism.L2.SG.Pf.RMeasP
end
end

