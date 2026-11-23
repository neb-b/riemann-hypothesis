module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemAd
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.Id

section Ad

variable {F : Type} [Field F] [NumberField F]

theorem memO {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  first
    | exact Iff.rfl
    | exact HeightOneSpectrum.mem_adicCompletionIntegers F v
    | simp [HeightOneSpectrum.mem_adicCompletionIntegers]

def evA (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evA_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evA v a = a v := rfl

theorem eq_of_evA {a b : Af F} (h : ∀ v, evA v a = evA v b) : a = b := by
  first
    | (ext v; exact h v)
    | exact Subtype.ext (funext h)
    | exact RestrictedProduct.ext h

def mkA (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (hc : ∀ v, Valued.v (c v) ≤ 1) :
    Af F :=
  ⟨c, Filter.Eventually.of_forall fun v => memO.2 (hc v)⟩

theorem mkA_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) (v : HeightOneSpectrum (𝓞 F)) : mkA c hc v = c v := rfl

theorem mkA_mem (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) : mkA c hc ∈ Formalism.UG.intAd F := by
  unfold Formalism.UG.intAd
  show ∀ v, mkA c hc v ∈ HeightOneSpectrum.adicCompletionIntegers F v
  intro v
  rw [mkA_apply]
  exact memO.2 (hc v)

theorem natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) :
    Valued.v ((g : ℕ) : v.adicCompletion F) ≤ 1 := memO.1 (natCast_mem _ g)

end Ad

theorem adOfLoc : AdOfLoc := by
  unfold AdOfLoc LocIdem AdIdem
  intro hL F _ _ g α β hg hα hβ
  have hα' : ∀ v, Valued.v (α v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, α v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hα) v
    exact memO.1 h0
  have hβ' : ∀ v, Valued.v (β v) ≤ 1 := by
    intro v
    have h0 := (show ∀ v, β v ∈ HeightOneSpectrum.adicCompletionIntegers F v from hβ) v
    exact memO.1 h0
  have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c₁ c₂ : v.adicCompletion F,
      Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α v) * (1 + (g : v.adicCompletion F) * c₁) ^ 2
          - 2 * (1 + (g : v.adicCompletion F) * c₁) * ((g : v.adicCompletion F) * c₂)
        = 1 + (g : v.adicCompletion F) * c₁ ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2
        = -((g : v.adicCompletion F) * c₂) ∧
      ((g : v.adicCompletion F) * c₂) ^ 2
          - (1 + (g : v.adicCompletion F) * α v) * ((g : v.adicCompletion F) * c₂)
            * (1 + (g : v.adicCompletion F) * c₁)
          + (g : v.adicCompletion F) * β v * (1 + (g : v.adicCompletion F) * c₁) ^ 2 = 0 := by
    intro v
    by_cases hv : Valued.v ((g : ℕ) : v.adicCompletion F) < 1
    · exact hL F v g (α v) (β v) hg hv (hα' v) (hβ' v)
    · have h1 : Valued.v ((g : ℕ) : v.adicCompletion F) = 1 :=
        le_antisymm (natCast_le_one v g) (not_lt.mp hv)
      have hg0 : ((g : ℕ) : v.adicCompletion F) ≠ 0 := by
        intro h
        rw [h, map_zero] at h1
        exact zero_ne_one h1
      have hu : 1 + (g : v.adicCompletion F) * -((g : v.adicCompletion F))⁻¹ = 0 := by
        rw [mul_neg, mul_inv_cancel₀ hg0, add_neg_cancel]
      refine ⟨-((g : v.adicCompletion F))⁻¹, 0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Valuation.map_neg, map_inv₀, h1, inv_one]
      · rw [map_zero]
        exact zero_le'
      · rw [hu]
        simp
      · rw [hu]
        simp
      · rw [hu]
        simp
  choose c₁ c₂ h1 h2 e1 e2 e3 using key
  refine ⟨mkA c₁ h1, mkA c₂ h2, mkA_mem c₁ h1, mkA_mem c₂ h2, ?_, ?_, ?_⟩
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e1 v
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      evA_apply, mkA_apply]
    exact e2 v
  · apply eq_of_evA
    intro v
    simp only [map_add (f := _), map_mul, map_sub, map_pow, map_one, map_natCast, map_neg, map_ofNat,
      map_zero, evA_apply, mkA_apply]
    exact e3 v

end PI.ScRefExists.Id
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLoc
section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace PI.ScRefExists.Id

theorem locIdem : LocIdem := by
  intro F _ _ v g α β hg hgv hα hβ
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  let ϖ : v.adicCompletionIntegers F := ⟨((g : ℕ) : v.adicCompletion F), (memO _).2 hgv.le⟩
  let aO : v.adicCompletionIntegers F := ⟨α, (memO _).2 hα⟩
  let bO : v.adicCompletionIntegers F := ⟨β, (memO _).2 hβ⟩
  have hϖ : ϖ ≠ 0 := by
    intro h
    have h' : ((g : ℕ) : v.adicCompletion F) = 0 := congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (by omega : g ≠ 0)) h'
  have h1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hgv
  haveI := PI.LocalEndW.isAdicComplete v ϖ hϖ h1
  let f : Polynomial (v.adicCompletionIntegers F) := X ^ 2 - C (1 + ϖ * aO) * X + C (ϖ * bO)
  have hf : f.Monic := by simp only [f]; monicity!
  have h0 : f.eval 0 ∈ Ideal.span {ϖ} := by
    have e : f.eval 0 = bO * ϖ := by
      simp only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring
    rw [e, Ideal.mem_span_singleton']
    exact ⟨bO, rfl⟩
  have hd : f.derivative.eval 0 = -(1 + ϖ * aO) := by simp [f]
  have hm : Ideal.Quotient.mk (Ideal.span {ϖ}) (-(1 + ϖ * aO)) = -1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), ← map_neg, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-aO, by ring⟩
  obtain ⟨ρ, hρ, hρI⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ}) f hf 0 h0
    (by rw [hd, hm]; exact isUnit_one.neg)
  rw [sub_zero, Ideal.mem_span_singleton'] at hρI
  obtain ⟨r0, rfl⟩ := hρI
  have hroot : (r0 * ϖ) ^ 2 - (1 + ϖ * aO) * (r0 * ϖ) + ϖ * bO = 0 := by
    have h : f.eval (r0 * ϖ) = 0 := hρ
    simpa only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] using h
  have hu : IsUnit (1 + ϖ * (aO - 2 * r0)) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hy : Valued.v ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
      (memO _).1 (aO - 2 * r0).2
    have hlt : Valued.v ((ϖ : v.adicCompletion F) *
        ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hgv
    exact (Valued.v).map_one_add_of_lt hlt
  obtain ⟨U, hU⟩ := hu
  obtain ⟨wO, hwO⟩ : ∃ w : v.adicCompletionIntegers F, w = ((U⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) := ⟨_, rfl⟩
  have huw : (1 + ϖ * (aO - 2 * r0)) * wO = 1 := by rw [← hU, hwO]; exact U.mul_inv
  obtain ⟨c1, hc1⟩ : ∃ c : v.adicCompletionIntegers F, c = -(aO - 2 * r0) * wO := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : v.adicCompletionIntegers F, c = r0 * wO := ⟨_, rfl⟩
  have hA : (1 + ϖ * aO) * (1 + ϖ * c1) ^ 2 - 2 * (1 + ϖ * c1) * (ϖ * c2) = 1 + ϖ * c1 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * (-(aO - 2 * r0) * wO)) * (1 - (1 + ϖ * aO))) * huw
  have hB : (ϖ * c2) ^ 2 - ϖ * bO * (1 + ϖ * c1) ^ 2 = -(ϖ * c2) := by
    rw [hc1, hc2]
    linear_combination (-(r0 * ϖ) * wO + ϖ * bO * (2 * wO - ((1 + ϖ * (aO - 2 * r0)) * wO - 1))) * huw
      + (-wO ^ 2) * hroot
  have hC : (ϖ * c2) ^ 2 - (1 + ϖ * aO) * (ϖ * c2) * (1 + ϖ * c1) + ϖ * bO * (1 + ϖ * c1) ^ 2 = 0 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * aO) * (r0 * ϖ) * wO - 2 * (ϖ * bO) * wO
      + ϖ * bO * ((1 + ϖ * (aO - 2 * r0)) * wO - 1)) * huw + wO ^ 2 * hroot
  refine ⟨(c1 : v.adicCompletion F), (c2 : v.adicCompletion F), (memO _).1 c1.2, (memO _).1 c2.2,
    ?_, ?_, ?_⟩
  · have e := congrArg (v.adicCompletionIntegers F).subtype hA
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hB
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hC
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at e
    exact e

end PI.ScRefExists.Id
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemTen
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Id

theorem fixInt : FixInt := by
  intro I s hs
  obtain ⟨a, ha⟩ := (I.cm.fixed (s : I.E)).mp hs
  have hs' : IsIntegral ℤ ((algebraMap I.F I.E).toIntAlgHom a) := by
    show IsIntegral ℤ (algebraMap I.F I.E a)
    rw [ha]
    exact NumberField.RingOfIntegers.isIntegral_coe s
  have hint : IsIntegral ℤ a :=
    (isIntegral_algHom_iff (algebraMap I.F I.E).toIntAlgHom (algebraMap I.F I.E).injective).mp hs'
  exact ⟨⟨a, hint⟩, ha⟩

theorem intF {F : Type} [Field F] [NumberField F] (r : 𝓞 F) :
    algebraMap F (Af F) (r : F) ∈ Formalism.UG.intAd F := by
  show ∀ v, _
  intro v
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

section Ten

variable (I : Formalism.MainNotions.S.AutInst)

def iA : Af I.F →ₐ[I.F] I.E ⊗[I.F] Af I.F := Algebra.TensorProduct.includeRight

def iE : I.E →+* I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F)

theorem iA_apply (x : Af I.F) : iA I x = (1 : I.E) ⊗ₜ[I.F] x :=
  Algebra.TensorProduct.includeRight_apply x

theorem iE_apply (e : I.E) : iE I e = e ⊗ₜ[I.F] (1 : Af I.F) :=
  Algebra.TensorProduct.includeLeftRingHom_apply e

theorem iE_alg (x : I.F) : iE I (algebraMap I.F I.E x) = iA I (algebraMap I.F (Af I.F) x) := by
  rw [iE_apply, iA_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem sig_iA (x : Af I.F) : sigA I (iA I x) = iA I x := by
  rw [iA_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem sig_iE (e : I.E) : sigA I (iE I e) = iE I (star e) := by
  rw [iE_apply, iE_apply]
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem iE_mem (θ : 𝓞 I.E) : iE I (θ : I.E) ∈ IntAf I.F I.E := by
  rw [iE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨(θ : I.E), θ, rfl⟩, rfl⟩)

theorem iA_mem {x : Af I.F} (hx : x ∈ Formalism.UG.intAd I.F) : iA I x ∈ IntAf I.F I.E := by
  rw [iA_apply]
  exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end Ten

theorem tenStep : TenStep := by
  intro hAd hFix I g θ hg _hsp hθ
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩⟩ := hθ
  have hgE : ((g : ℕ) : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs2 : star (t2 : I.E) = t2 := by
    have h1 : star ((θ : I.E) * star (θ : I.E)) = (θ : I.E) * star (θ : I.E) := by
      rw [star_mul, star_star]
    rw [ht2, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  have hs3 : star (t3 : I.E) = t3 := by
    have h1 : star (1 - (θ : I.E) - star (θ : I.E)) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [star_sub, star_sub, star_one, star_star]
      ring
    rw [ht3, star_mul, star_natCast, mul_comm] at h1
    exact mul_left_cancel₀ hgE h1
  obtain ⟨a2, ha2⟩ := hFix I t2 hs2
  obtain ⟨a3, ha3⟩ := hFix I t3 hs3
  have hαi : -algebraMap I.F (Af I.F) (a3 : I.F) ∈ Formalism.UG.intAd I.F :=
    (Formalism.UG.intAd I.F).neg_mem (intF a3)
  have hβi : algebraMap I.F (Af I.F) (a2 : I.F) ∈ Formalism.UG.intAd I.F := intF a2
  obtain ⟨C₁, C₂, hC₁, hC₂, hi, hii, hiii⟩ := hAd I.F g _ _ hg hαi hβi
  obtain ⟨W, hWd⟩ : ∃ W : Af I.F, W = 1 + (g : Af I.F) * C₁ := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : Af I.F, Q = (g : Af I.F) * C₂ := ⟨_, rfl⟩
  obtain ⟨A0, hA0d⟩ : ∃ A0 : Af I.F,
      A0 = 1 + (g : Af I.F) * -algebraMap I.F (Af I.F) (a3 : I.F) := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0 : Af I.F, B0 = (g : Af I.F) * algebraMap I.F (Af I.F) (a2 : I.F) :=
    ⟨_, rfl⟩
  rw [← hWd, ← hQd, ← hA0d] at hi
  rw [← hWd, ← hQd, ← hB0d] at hii
  rw [← hWd, ← hQd, ← hA0d, ← hB0d] at hiii
  have hi' := congrArg (iA I) hi
  have hii' := congrArg (iA I) hii
  have hiii' := congrArg (iA I) hiii
  simp only [map_mul, map_add (f := _), map_sub, map_pow, map_neg, map_ofNat, map_zero] at hi' hii' hiii'
  have hA : iA I A0 = iE I (θ : I.E) + iE I (star (θ : I.E)) := by
    have e1 : A0 = algebraMap I.F (Af I.F) (1 - (g : I.F) * (a3 : I.F)) := by
      rw [hA0d, map_sub, map_one, map_mul, map_natCast]
      ring
    have e2 : algebraMap I.F I.E (1 - (g : I.F) * (a3 : I.F)) = (θ : I.E) + star (θ : I.E) := by
      rw [map_sub, map_one, map_mul, map_natCast, ha3]
      linear_combination ht3
    rw [e1, ← iE_alg, e2, map_add (f := _)]
  have hB : iA I B0 = iE I (θ : I.E) * iE I (star (θ : I.E)) := by
    have e1 : B0 = algebraMap I.F (Af I.F) ((g : I.F) * (a2 : I.F)) := by
      rw [hB0d, map_mul, map_natCast]
    have e2 : algebraMap I.F I.E ((g : I.F) * (a2 : I.F)) = (θ : I.E) * star (θ : I.E) := by
      rw [map_mul, map_natCast, ha2, ht2]
    rw [e1, ← iE_alg, e2, map_mul]
  rw [hA] at hi' hiii'
  rw [hB] at hii' hiii'
  have hWi : W ∈ Formalism.UG.intAd I.F := by
    rw [hWd]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ g) hC₁)
  have hQi : Q ∈ Formalism.UG.intAd I.F := by
    rw [hQd]
    exact mul_mem (natCast_mem _ g) hC₂
  refine ⟨iE I (θ : I.E) * iA I W - iA I Q, ?_, ?_, ?_, ?_⟩
  · exact sub_mem (mul_mem (iE_mem I θ) (iA_mem I hWi)) (iA_mem I hQi)
  · linear_combination (iE I (θ : I.E)) * hi' + hii'
  · rw [map_sub, map_mul, sig_iE, sig_iA, sig_iA]
    linear_combination hiii'
  · refine ⟨iE I (θ : I.E) * iA I C₁ - iA I C₂,
      sub_mem (mul_mem (iE_mem I θ) (iA_mem I hC₁)) (iA_mem I hC₂), ?_⟩
    have hW' : iA I W = 1 + (g : I.E ⊗[I.F] Af I.F) * iA I C₁ := by
      rw [hWd, map_add (f := _), map_one, map_mul, map_natCast]
    have hQ' : iA I Q = (g : I.E ⊗[I.F] Af I.F) * iA I C₂ := by
      rw [hQd, map_mul, map_natCast]
    show iE I (θ : I.E) * iA I W - iA I Q - iE I (θ : I.E) = _
    rw [hW', hQ']
    ring

end PI.ScRefExists.Id
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Ap (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Subalgebra (𝓞 I.E) I.E where
  carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E)}
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, a * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t * y) * ha + (a : I.E) * hb
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t : I.E) * ha + (↑s : I.E) * hb
  algebraMap_mem' := by
    intro a
    exact ⟨1, Nat.coprime_one_left p, a, by simp⟩

def LA (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Submodule (Ap I p) (Fin I.n → I.E) :=
  Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E))

def ApPID : Prop := ∀ (I : Formalism.MainNotions.S.AutInst) (p : ℕ), p.Prime → IsPrincipalIdealRing (Ap I p)

def WFrame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w wd : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) ∧
      (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) ∧
      (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)

def PPAssemble : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M →
    (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) →
    (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) →
    (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) →
    (∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)) →
    Concl I (p ^ m) r k θ e f M

theorem gwpp_of (h1 : WFrame) (h2 : PPAssemble) : GWpp := by
  intro I p m r k θ e f M hp hm hH
  obtain ⟨_, _, _, hn, hee, hff, hef, hM, hL⟩ := id hH
  have hMp : Nat.Coprime M p :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hM
  obtain ⟨w, wd, hw, horth, hdual, hspan⟩ := h1 I p r k e f M hp hn hee hff hef hMp hL
  exact h2 I p m r k θ e f M w wd hp hm hH hw horth hdual hspan

end PI.ScRefExists.Sk
end
end

