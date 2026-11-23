module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChowSecDvd.proof (h₁ : IncidenceNull.Statement) : ChowSecDvd.Statement := by
  intro k E _ _ _ n e Q g y _ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  set I := secIdeal QE y with hI
  set ι : E →+* SecAlg QE y := algebraMap E (SecAlg QE y) with hι
  set x : Fin n → SecAlg QE y := secCoord QE y with hx
  have hmk : ∀ p : MvPolynomial (Fin n) E, Ideal.Quotient.mk I p = eval₂ ι x p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [eval₂_C, hι]; rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, hp, eval₂_mul, eval₂_X]; rfl
  have hlin : ∀ u : Fin n → E, ∑ j, ι (u j) * x j = Ideal.Quotient.mk I (linForm u) := by
    intro u
    simp [hmk, linForm, eval₂_sum, mul_comm]
  have hchart : ∑ j, ι (y (.inr j)) * x j = 1 := by
    rw [hlin, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hform : ∀ i, ∑ j, ι (y (.inl (i, j))) * x j = 0 := by
    intro i
    rw [hlin, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  set θ : MvPolynomial (Fin n) (SecAlg QE y) := ∑ j, X j * C (x j) with hθ
  set c : k →+* MvPolynomial (Fin n) (SecAlg QE y) := (C : SecAlg QE y →+* _).comp (ι.comp (algebraMap k E))
    with hc
  let vφ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2 - θ * C (ι (y (.inr ij.2)))) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  let vψ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  set φ := eval₂Hom c vφ with hφ
  set ψ := eval₂Hom c vψ with hψ

  have hker : incIdeal Q (e + 1) ≤ RingHom.ker φ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, coe_eval₂Hom, eval₂_rename]
      have h : eval₂ c (vφ ∘ Sum.inl) q = C (Ideal.Quotient.mk I (q.map (algebraMap k E))) := by
        rw [hmk, eval₂_map, eval₂_comp_left]
        rfl
      rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
      simp only [map_mul, hφ, eval₂Hom_X', vφ, Sum.elim_inl, Sum.elim_inr]
      refine Fin.cases ?_ (fun i => ?_) i
      · show ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) = 0
        have h : ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) =
            θ - θ * C (∑ j, ι (y (.inr j)) * x j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_mul, Finset.mul_sum]
          rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
          conv_rhs => rw [hθ]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h, hchart, map_one, mul_one, sub_self]
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [Fin.cases_succ, ← map_mul, ← map_sum, hform, map_zero]
  obtain ⟨M, hM⟩ := h₁ k n (e + 1) Q g hg
  set G := φ (rename Sum.inr g) with hG
  have hGx : ∀ j, G ^ M * C (x j) ^ M = 0 := by
    intro j
    have := hker (hM j)
    rw [RingHom.mem_ker, map_pow, map_mul, hφ, eval₂Hom_X'] at this
    rw [← mul_pow]
    exact this
  have hG0 : G ^ M = 0 := by
    have h1 : Ideal.span (Set.range fun j => (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))) = ⊤ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Ideal.eq_top_iff_one, ← map_one C, ← hchart, map_sum]
      exact sum_mem fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := Ideal.span_pow_eq_top _ h1 M
    have h3 : (1 : MvPolynomial (Fin n) (SecAlg QE y)) ∈
        Ideal.span ((fun z => z ^ M) '' Set.range fun j => C (x j)) := by
      rw [h2]; exact Submodule.mem_top
    have key : ∀ z ∈ Ideal.span ((fun z => z ^ M) '' Set.range fun j =>
        (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))), G ^ M * z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hz
        exact hGx j
      | zero => exact mul_zero _
      | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
      | smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
    simpa using key 1 h3

  set π := Ideal.Quotient.mk (Ideal.span {θ}) with hπ
  have hπθ : π θ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self θ)
  have hcomp : π.comp φ = π.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [hφ, hψ]
    · intro v
      rcases v with j | ⟨i, j⟩
      · simp [hφ, hψ, vφ, vψ]
      · refine Fin.cases ?_ (fun i => ?_) i
        · set_option synthInstance.maxHeartbeats 100000 in
            simp [hφ, hψ, vφ, vψ, hπθ]
        · simp [hφ, hψ, vφ, vψ]
  have hspec : ψ (rename Sum.inr g) =
      (specRest (algebraMap k E) g y).map (algebraMap E (SecAlg QE y)) := by
    rw [hψ, coe_eval₂Hom, eval₂_rename]
    unfold specRest
    rw [eval₂_comp_left]
    congr 1
    · exact RingHom.ext fun a => by simp [hc, hι]
    · funext ij
      obtain ⟨i, j⟩ := ij
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [vψ, hι]
  refine ⟨M + 1, M.succ_pos, ?_⟩
  have hz : π (ψ (rename Sum.inr g) ^ (M + 1)) = 0 := by
    rw [map_pow, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, pow_succ, ← map_pow, ← hG, hG0,
      map_zero, zero_mul]
  rw [← hspec, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenChowIrreducible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenChowIrreducible

variable {n e : ℕ}

theorem map_specRest {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;> simp [eval₂_mul, hp]

theorem constantCoeff_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {δ : ℕ}
    (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) R} (hf : IsMultiHomog δ f)
    (y : Par e n → S) : constantCoeff (specRest φ f y) = 0 := by
  unfold specRest
  rw [← coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [coe_eval₂Hom, eval₂_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨j, hj⟩ : ∃ j, d (0, j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := congrFun (hf (mem_support_iff.mp hd)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero] at h0
    · omega
    · rintro ⟨i, j'⟩ _
      simp only [groupWeight, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi; simp [hcon j']
      · simp [Ne.symm hi]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (0, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

def parVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Fin n ⊕ Par e n :=
  Fin.cases (motive := fun _ => Fin n ⊕ Par e n) (.inl ij.2) (fun i => .inr (.inl (i, ij.2))) ij.1

theorem parVar_injective : Function.Injective (parVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parVar]

theorem specRest_X {k : Type*} [Field k] (f : MvPolynomial (Fin (e + 1) × Fin n) k) :
    specRest (algebraMap k (MvPolynomial (Par e n) k)) f X =
      sumAlgEquiv k (Fin n) (Par e n) (rename (parVar e n) f) := by
  unfold specRest
  rw [MvPolynomial.algebraMap_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;>
      simp [eval₂_mul, hp, parVar, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]

theorem proof (h1 : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement)
    (h2 : GroundTheory.Heights₂.Heights.ChowFormMultiHomog.Statement) : GenChowIrreducible.Statement := by
  intro k _ n e Q g hQ hg

  have hspan : GroundTheory.Heights₂.Heights.incIdeal Q (e + 1) = Ideal.span {g} := by
    ext p
    rw [Ideal.mem_span_singleton, ← hg.2 p]
    simp [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have := h1 k n (e + 1) Q hQ.isPrime hQ.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hg.1).mp this
  obtain ⟨δ, hδ, hhom⟩ := h2 k n (e + 1) Q g hQ hg

  have hren : Prime (rename (parVar e n) g) := by
    have e1 : rename (parVar e n) g = rename ((↑) : Set.range (parVar e n) → _)
        (rename (Equiv.ofInjective _ parVar_injective) g) := by
      rw [rename_rename]; rfl
    rw [e1, prime_rename_iff]
    exact (MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective _ parVar_injective))).mpr hprime
  have hpP : Prime (specRest (algebraMap k (MvPolynomial (Par e n) k)) g X) := by
    rw [specRest_X]
    exact (MulEquiv.prime_iff (sumAlgEquiv k (Fin n) (Par e n))).mpr hren
  set p := specRest (algebraMap k (MvPolynomial (Par e n) k)) g X with hp
  have hq : specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
      p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) := by
    rw [hp, map_specRest, ← IsScalarTower.algebraMap_eq]; rfl

  let _ : Algebra (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))
      (MvPolynomial (Fin n) (GenParField k e n)) := algebraMvPolynomial
  have hc0 : constantCoeff p = 0 := constantCoeff_specRest _ hδ hhom _
  have hdisj : Disjoint
      (((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)) : Submonoid _) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))) ↑(Ideal.span {p}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hmem
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hmem
    obtain ⟨s, hs⟩ := hmem
    have := congrArg constantCoeff hs
    rw [constantCoeff_C, map_mul, hc0, zero_mul] at this
    exact nonZeroDivisors.ne_zero hr this
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)))
    (MvPolynomial (Fin n) (GenParField k e n)) (Ideal.span {p})
    ((Ideal.span_singleton_prime hpP.ne_zero).mpr hpP) hdisj
  rw [Ideal.map_span, Set.image_singleton, algebraMap_def] at hpr
  have hq0 : p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) ≠ 0 := by
    intro h
    apply hpP.ne_zero
    apply map_injective _ (IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n))
    rw [h, map_zero]
  rw [hq]
  exact ((Ideal.span_singleton_prime hq0).mp hpr).irreducible

end GenChowIrreducible

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormIdentity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Lemmas

variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

def chartVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (.inr ij.2) (fun i => .inl (i, ij.2)) ij.1

theorem chartVar_injective (e n : ℕ) : Function.Injective (chartVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;>
    simp_all [chartVar, Fin.cases_zero, Fin.cases_succ]

theorem parToFrac_algebraMap' (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by
  rw [parToFrac, IsLocalization.lift_eq]

theorem kToFrac_algebraMap (e n : ℕ) (a : 𝓞 K) :
    kToFrac K e n (algebraMap (𝓞 K) K a) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (C a) := by
  rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]

theorem eval_specRest_chart (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    eval (fun j => parYF K e n (.inr j))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename (chartVar e n) g) := by
  have h : ((eval fun j => parYF K e n (.inr j)).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp (rename (chartVar e n)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [chartVar, parYF]
  exact congrArg (fun φ => φ g) h

theorem eval_specRest_lin (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by
  have h : ((eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))).comp
      ((eval₂Hom (C.comp (kToFrac K e n)) (fun ij => Fin.cases
        (motive := fun _ => MvPolynomial (Fin n) (ParFrac K e n)) (X ij.2)
        (fun i => C (parYF K e n (.inl (i, ij.2)))) ij.1)).comp (map (algebraMap (𝓞 K) K)))) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp
        ((rename (Sum.inl : Fin e × Fin n → Par e n)).toRingHom.comp (bind₁ (specFirstVar u)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
    · simp [kToFrac_algebraMap]
    · rcases ij with ⟨i, j⟩
      induction i using Fin.cases <;> simp [specFirstVar, parYF, kToFrac_algebraMap]
  exact congrArg (fun φ => φ g) h

theorem secLin_eq_sum {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secLin, linForm, map_sum, map_mul]
  rfl

theorem chart_sum_eq_one {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)}
    {y : Par e n → R} : ∑ j, algebraMap R (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  rw [← secLin_eq_sum]
  have hmem : chartForm y - 1 ∈ secIdeal Q y := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have h := Ideal.Quotient.eq.mpr hmem
  rw [map_one] at h
  exact h

end Lemmas

theorem NormIdentity.proof (hcn : ChowNormForm.Statement) (hfin : SecBFinite.Statement)
    (htf : SecBTorsionFree.Statement) (hgen : SecBGeneric.Statement)
    (hloc : NormFormLocalization.Statement) (hev : NormFormEval.Statement)
    (hai : ParAlgIndep.Statement) (hfr : ParFracIsFractionRing.Statement)
    (hdvr : ParDVRIsDVR.Statement) : NormIdentity.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  obtain ⟨φ, hφc, hφr, hφloc⟩ := hgen K n e I v hI
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I _ v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  let _iRF : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have hFR : IsFractionRing (ParDVR e n v) (ParFrac K e n) := hfr K e n v
  let _iKF : Algebra K (ParFrac K e n) := (kToFrac K e n).toAlgebra
  let _iBL : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have _t1 : IsScalarTower (ParDVR e n v) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) :=
    IsScalarTower.of_algebraMap_eq (R := ParDVR e n v) (S := SecB e I v)
      (A := SecAlg (idealF e I) (parYF K e n)) fun r => (hφr r).symm
  have hNL := hloc (ParDVR e n v) (ParFrac K e n) (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) n
    (secCoord (modelR e I v) (parY e n v))
  have hxs : (fun j => algebraMap (SecB e I v) (SecAlg (idealF e I) (parYF K e n))
      (secCoord (modelR e I v) (parY e n v) j)) = secCoord (idealF e I) (parYF K e n) := funext hφc
  rw [hxs] at hNL
  obtain ⟨-, c, -, hcn'⟩ := hcn K (ParFrac K e n) n e I (g.map (algebraMap (𝓞 K) K)) (parYF K e n)
    (hai K e n) hI hf
  set P := normForm (R := ParDVR e n v) (SecB e I v) (secCoord (modelR e I v) (parY e n v)) with hP
  replace hcn' : specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n) =
      C c * P.map (algebraMap (ParDVR e n v) (ParFrac K e n)) := by
    rw [hNL]
    exact hcn'

  have hevP : ∀ z : Fin n → ParDVR e n v,
      eval (fun j => parToFrac e n v (z j)) (P.map (algebraMap (ParDVR e n v) (ParFrac K e n))) =
        parToFrac e n v (Algebra.norm (ParDVR e n v)
          (∑ j, algebraMap (ParDVR e n v) (SecB e I v) (z j) * secCoord (modelR e I v) (parY e n v) j)) := by
    intro z
    rw [eval_map, ← hev (ParDVR e n v) (SecB e I v) n _ z, ← hP]
    show eval₂ _ _ P = parToFrac e n v (eval₂ (RingHom.id _) z P)
    rw [hom_eval₂]
    rfl

  have hT := congrArg (eval fun j => parYF K e n (.inr j)) hcn'
  rw [eval_specRest_chart, map_mul, eval_C] at hT
  have hTpt : (fun j => parYF K e n (.inr j)) = fun j => parToFrac e n v (parY e n v (.inr j)) := by
    funext j
    rw [parY, parToFrac_algebraMap']
    rfl
  rw [hTpt, hevP, chart_sum_eq_one, map_one, map_one, mul_one] at hT

  have hU := congrArg (eval fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) hcn'
  rw [eval_specRest_lin, map_mul, eval_C] at hU
  have hUpt : (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j))) =
      fun j => parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) (u j)) := by
    funext j
    rw [kToFrac_algebraMap, IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), parToFrac_algebraMap']
    rfl
  rw [hUpt, hevP, ← secLin_eq_sum, ← hT, ← parToFrac_algebraMap', ← parToFrac_algebraMap', ← map_mul] at hU
  have hinj : Function.Injective (parToFrac e n v) := IsFractionRing.injective (ParDVR e n v) (ParFrac K e n)
  have hUR := hinj hU

  obtain ⟨m, hm⟩ := hprim
  have hnot : rename (chartVar e n) g ∈ (parPrime e n v).primeCompl := by
    intro hmem
    have hmem' : rename (chartVar e n) g ∈ Ideal.map C v.asIdeal := hmem
    rw [MvPolynomial.mem_map_C_iff] at hmem'
    have hmem := hmem'
    have := hmem (Finsupp.mapDomain (chartVar e n) m)
    rw [coeff_rename_mapDomain _ (chartVar_injective e n)] at this
    exact hm this
  have hunit : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (chartVar e n) g)) :=
    IsLocalization.map_units (ParDVR e n v) (⟨_, hnot⟩ : (parPrime e n v).primeCompl)
  exact ⟨hunit.unit, hUR⟩

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PResidueAlgIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ResidueAlgIndep.proof : ResidueAlgIndep.Statement := by
  intro K _ _ e n v
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal) p

  have hext : (eval₂Hom ((algebraMap k E).comp (algebraMap (𝓞 K) k)) (parYκ e n v)) =
      (algebraMap R E).comp (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) R]
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ a
    · simp [parYκ, parY, R, E]
  have key : aeval (parYκ e n v) (MvPolynomial.map (algebraMap (𝓞 K) k) q) =
      algebraMap R E (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R q) := by
    rw [aeval_def, eval₂_map]
    exact congrArg (fun φ => φ q) hext
  rw [key, Ideal.algebraMap_residueField_eq_zero] at hp
  have hq : q ∈ parPrime e n v := by
    have h2 : (IsLocalRing.maximalIdeal R).comap (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) =
        parPrime e n v :=
      Localization.AtPrime.under_maximalIdeal
    rw [← h2]
    exact hp
  rw [parPrime, MvPolynomial.mem_map_C_iff] at hq
  ext m
  simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
    Ideal.algebraMap_residueField_eq_zero.mpr (hq m)

end

end GroundTheory.Heights₂.Heights.Vertical
end

