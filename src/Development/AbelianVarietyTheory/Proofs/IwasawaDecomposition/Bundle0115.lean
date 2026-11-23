module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActsTriviallyOnDiscriminantGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclE_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) a) =
      inclE (F := F) (v.adicCompletion F) (σ a) := by
  simp [sigR, inclE]

theorem sigR_mem_intV_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] v.adicCompletion F}
    (hs : s ∈ intV E v) : sigR σ (v.adicCompletion F) s ∈ intV E v := by
  have key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v
      rw [sigR_inclE_adic]
      have h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) :=
        (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
      exact Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _
        ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v
      simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

theorem mul_eq_unit_mul_of_triple_product_one {A : Type} [CommRing A] (a b P Q T : A) (h : P * Q * T = 1) :
    a * b = T * ((a * P) * (b * Q)) := by linear_combination (-(a * b)) * h

theorem eq_one_add_mul_neg_of_add_mul_eq_one {A : Type} [CommRing A] (a T S : A) (h : a + T * S = 1) : a = 1 + T * (-S) := by
  linear_combination h

theorem mul_sub_eq_of_triple_product_one {A : Type} [CommRing A] (P Q T d e : A) (h : P * Q * T = 1) (hd : d = 1 + T * e) :
    P * (d * Q - Q) = e := by linear_combination (P * Q) * hd + e * h

end SlopeTestRemainingChoices


set_option maxHeartbeats 1000000 in
theorem uloc_acts_trivially_on_dual_quotient {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (hqp : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T ≠ 0)
    (hLb : S.Lb = rll_dLat n ((p : E)⁻¹))
    (hdual : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hH : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, zero_mul])
  have hq0 : (q : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, mul_zero])
  have hΛ : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hLb]; exact rll_mem_loc_dLat n v _ (inv_ne_zero hp0) z
  have hΛ' : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)) ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) (q : E) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hdual]; exact rll_mem_loc_dLat n v _ hq0 z
  rw [S.UlocAlt v hv] at hx
  obtain ⟨⟨hU, hstL⟩, hstL', hfix⟩ := hx
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hιdef
  set ℓ := lastIdx n with hℓ
  set X := (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) with hX
  have hQQ : ι (q : E) * ι ((q : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have hPQi : ι ((p : E)⁻¹) * ι ((q : E)⁻¹) * (T : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [← map_natCast ι T, ← map_mul, ← map_mul, ← hpq]
    rw [show (p : E)⁻¹ * (q : E)⁻¹ * ((p : E) * (q : E)) = 1 by field_simp, map_one]
  have hPQ : ι (p : E) * ι (q : E) = (T : E ⊗[F] v.adicCompletion F) := by
    rw [← map_mul, hpq, map_natCast]

  set w : Fin n → E ⊗[F] v.adicCompletion F := Pi.single ℓ (ι ((q : E)⁻¹)) with hwdef
  have hw : w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := by
    refine (hΛ' w).2 ⟨fun i hi => ?_, ?_⟩
    · rw [hwdef, Pi.single_eq_of_ne hi]; exact zero_mem _
    · rw [hwdef, Pi.single_eq_same, hQQ]; exact one_mem _

  have hdec : ∀ z ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z ℓ ∧
      z - (r : E ⊗[F] v.adicCompletion F) • w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    intro z hz
    refine ⟨⟨ι (q : E) * z ℓ, ((hΛ' z).1 hz).2⟩, rfl, (hΛ _).2 ⟨fun i hi => ?_, ?_⟩⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact ((hΛ' z).1 hz).1 i hi
    · have h0 : z ℓ - (ι (q : E) * z ℓ) * ι ((q : E)⁻¹) = 0 := by linear_combination (-z ℓ) * hQQ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_same]
      rw [h0, mul_zero]; exact zero_mem _

  set m := S.fT v hv ⟨w, hw⟩ with hmdef
  have hf : ∀ z : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z.1 ℓ ∧ S.fT v hv z = r • m := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr, hu⟩ := hdec z hz
    refine ⟨r, hr, ?_⟩
    have h1 := S.fT_L v hv ((⟨z, hz⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)))) - r • (⟨w, hw⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))))) hu
    rw [map_sub] at h1
    rw [LinearMap.map_smul] at h1
    rw [sub_eq_zero] at h1
    exact h1
  have hm0 : m ≠ 0 := by
    intro h0
    apply S.fT_ne v hv
    refine LinearMap.ext fun z => ?_
    obtain ⟨r, -, hr⟩ := hf z
    rw [hr, h0, LinearMap.zero_apply]
    exact smul_zero r

  have hXw : X *ᵥ w = fun i => X i ℓ * ι ((q : E)⁻¹) := by
    funext i
    show (fun j => X i j) ⬝ᵥ Pi.single ℓ (ι ((q : E)⁻¹)) = _
    rw [dotProduct_single]
  have hxw : X *ᵥ w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := (hstL' w).1 hw
  have hb : ∀ i, i ≠ ℓ → X i ℓ * ι ((q : E)⁻¹) ∈ intV E v := by
    intro i hi
    have h1 := ((hΛ' _).1 hxw).1 i hi
    rw [congrFun hXw i] at h1
    exact h1
  have hXwi : ∀ i, (X *ᵥ w) i = X i ℓ * ι ((q : E)⁻¹) := fun i => congrFun hXw i
  have hd : X ℓ ℓ ∈ intV E v := by
    have h1 := ((hΛ' _).1 hxw).2
    rw [hXwi ℓ, mul_left_comm, hQQ, mul_one] at h1
    exact h1
  have h2 : ((⟨X ℓ ℓ, hd⟩ : intV E v) - 1) • m = 0 := by
    obtain ⟨r, hr, hrm⟩ := hf ⟨X *ᵥ w, hxw⟩
    have hr' : r = ⟨X ℓ ℓ, hd⟩ := by
      apply Subtype.ext
      rw [hr]
      show ι (q : E) * (X *ᵥ w) ℓ = X ℓ ℓ
      rw [hXwi ℓ, mul_left_comm, hQQ, mul_one]
    have hfx := hfix ⟨w, hw⟩
    rw [sub_smul, one_smul, ← hr', ← hrm, sub_eq_zero]
    exact hfx
  have hU' : cT (sigR σ (v.adicCompletion F)) X * X = 1 := by
    have h1 : cT (sigR σ (v.adicCompletion F)) X * (1 : Matrix (Fin n) (Fin n) E).map ι * X =
        (1 : Matrix (Fin n) (Fin n) E).map ι := hU
    rwa [Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_one] at h1
  have hsum : ∑ j, sigR σ (v.adicCompletion F) (X j ℓ) * X j ℓ = 1 := by
    have h1 := congrFun (congrFun hU' ℓ) ℓ
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simpa only [cT, Matrix.transpose_apply, Matrix.map_apply] using h1
  have hs : ∀ a : E, sigR σ (v.adicCompletion F) (ι a) = ι (σ a) := fun a => sigR_inclE_adic σ v a
  have hsq : σ (q : E) = p := by rw [hqp, hσ]
  have hsQi : sigR σ (v.adicCompletion F) (ι ((q : E)⁻¹)) = ι ((p : E)⁻¹) := by rw [hs, map_inv₀, hsq]
  have hc' : -∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))
      ∈ intV E v :=
    neg_mem (sum_mem fun j hj => mul_mem (sigR_mem_intV_adic σ v (hb j (Finset.ne_of_mem_erase hj)))
      (hb j (Finset.ne_of_mem_erase hj)))
  have h3 : sigR σ (v.adicCompletion F) (X ℓ ℓ) * X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) *
      (-∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))) := by
    apply eq_one_add_mul_neg_of_add_mul_eq_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)] at hsum
    rw [Finset.mul_sum]
    convert hsum using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hsQi]
    exact (mul_eq_unit_mul_of_triple_product_one _ _ _ _ _ hPQi).symm
  obtain ⟨e, he⟩ := hH m hm0 ⟨X ℓ ℓ, hd⟩ ⟨_, hc'⟩ h2 h3
  have he' : X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := he
  have hwΛ : X *ᵥ w - w ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    refine (hΛ _).2 ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.sub_apply, hXwi i, hwdef, Pi.single_eq_of_ne hi, sub_zero]
      exact hb i hi
    · rw [Pi.sub_apply, hXwi ℓ, hwdef, Pi.single_eq_same, mul_sub_eq_of_triple_product_one _ _ _ _ _ hPQi he']
      exact e.2
  intro y hy
  obtain ⟨r, -, hu⟩ := hdec y hy
  have hsplit : X *ᵥ y - y = (X *ᵥ (y - (r : E ⊗[F] v.adicCompletion F) • w) - (y - (r : E ⊗[F] v.adicCompletion F) • w)) +
      (r : E ⊗[F] v.adicCompletion F) • (X *ᵥ w - w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [hsplit]
  exact add_mem (sub_mem ((hstL _).1 hu) hu) (Submodule.smul_mem _ r hwΛ)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
section
noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


open Classical in
def patchAt (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  ⨅ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (if Q = P then A else B)

end GlobalTheory.InertExchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeLatticeDeterminantClass_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  first | exact @GlobalTheory.Mem.Chr.relDetT_laws | exact GlobalTheory.Mem.Chr.relDetT_laws | (intros; apply GlobalTheory.Mem.Chr.relDetT_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem lamS_succ_lt (R : Ranks) (P : HCParam R) (i j : Fin R.r) (hij : j.val = i.val + 1) :
    lamS R P j < lamS R P i := by
  have hk : R.m + 3 ≤ R.k := R.m_add_three_le_k
  have hm : 2 ≤ R.m := R.two_le_m
  have hjr : j.val < R.k + R.m - 1 := j.isLt
  have hu : ∀ a b : Fin R.k, a.val = b.val → P.u a = P.u b := fun a b h => by rw [Fin.ext h]
  have hb : ∀ a b : Fin R.m, a.val = b.val → P.b a = P.b b := fun a b h => by rw [Fin.ext h]
  unfold Formalism.MainNotions.S.lamS
  by_cases hj : j.val < R.k - 1
  · have hi : i.val < R.k - 1 := by omega
    rw [dite_eq_left hj, dite_eq_left hi]
    have key : P.v ⟨j.val, hj⟩ < P.v ⟨i.val, hi⟩ :=
      calc P.v ⟨j.val, hj⟩ < P.u ⟨j.val, by omega⟩ := P.u_gt_v ⟨j.val, hj⟩
        _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp [hij])
        _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
    exact_mod_cast key
  · by_cases hi : i.val < R.k - 1
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_left hi]
      have key : -P.b ⟨j.val - (R.k - 1), hj0⟩ < P.v ⟨i.val, hi⟩ :=
        calc -P.b ⟨j.val - (R.k - 1), hj0⟩ = -P.b ⟨0, by omega⟩ :=
            congrArg (fun x => -x) (hb _ _ (show j.val - (R.k - 1) = 0 by omega))
          _ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt (by omega) (by omega)
          _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp; omega)
          _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
      have := (Rat.cast_lt (K := ℝ)).mpr key
      push_cast at this
      exact this
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      have hi0 : i.val - (R.k - 1) < R.m := by omega
      have hi1 : i.val - (R.k - 1) + 1 < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_right hi, dite_eq_left hi0]
      have h1 := P.gap_be ⟨i.val - (R.k - 1), hi0⟩
      have h2 := P.gap_eb ⟨i.val - (R.k - 1), hi0⟩ hi1
      have h3 : P.b ⟨i.val - (R.k - 1) + 1, hi1⟩ = P.b ⟨j.val - (R.k - 1), hj0⟩ := hb _ _ (by simp; omega)
      have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
      have key : P.b ⟨i.val - (R.k - 1), hi0⟩ < P.b ⟨j.val - (R.k - 1), hj0⟩ := by
        rw [← h3]; linarith
      have := (Rat.cast_lt (K := ℝ)).mpr key
      linarith

theorem lamS_int (R : Ranks) (P : HCParam R) (i : Fin R.r) : ∃ z : ℤ, lamS R P i = (z : ℝ) := by
  unfold Formalism.MainNotions.S.lamS
  split_ifs with h h'
  · obtain ⟨z, hz⟩ := P.v_int ⟨i.val, h⟩
    exact ⟨z, by rw [hz, Rat.cast_intCast]⟩
  · obtain ⟨z, hz⟩ := P.b_int ⟨i.val - (R.k - 1), h'⟩
    exact ⟨-z, by rw [hz, Rat.cast_intCast]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem lamSH_isHCParam (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (lamSH R P) := by
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact lamS_succ_lt R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) (Fin.castSucc i))
      (Fin.cast (Formalism.MainNotions.S.dimS_eq R) i.succ) (by simp)
  · intro a
    obtain ⟨z, hz⟩ := lamS_int R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a)
    obtain ⟨w, hw⟩ := R.k_even
    have hk : (R.k : ℝ) = 2 * w := by rw [hw]; push_cast; ring
    refine ⟨z - R.rS - w, ?_⟩
    show lamS R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) - _ = _
    rw [hz]
    push_cast
    rw [hk]
    ring

theorem fdegHC_pos_of_injective {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hlam h))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : (a : ℕ) < b := hb.2
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

theorem lamSH_isHCParam_and_trueDsig_pos :
    ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  intro R P
  refine ⟨lamSH_isHCParam R P, ?_⟩
  exact fdegHC_pos_of_injective _ (lamSH_isHCParam R P).1.injective

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariantStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_comparison_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∀ u : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull (U'.gt e).pG.left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull (U.gt e).pG.left), u.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL')) →
    ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G)
      (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U.gt e).i) * y).left z (fun _ => jM) (fun _ _ => jM') = gw u y.left z (fun _ => jM) (fun _ _ => jM') := by
  first | exact @GlobalTheory.comparison_sq_torus_invariant | exact GlobalTheory.comparison_sq_torus_invariant | (intros; apply GlobalTheory.comparison_sq_torus_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubicalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_carries_square_cubical : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_carries_sq_cube | exact GlobalTheory.sq_iso_carries_sq_cube | (intros; apply GlobalTheory.sq_iso_carries_sq_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwiseStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_respects_symmetry_pointwise | exact GlobalTheory.sq_iso_respects_symmetry_pointwise | (intros; apply GlobalTheory.sq_iso_respects_symmetry_pointwise <;> assumption)
end

