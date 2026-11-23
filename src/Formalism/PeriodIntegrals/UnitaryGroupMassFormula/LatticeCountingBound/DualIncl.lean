module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan

@[expose] public section

noncomputable section

open NumberField Matrix TensorProduct

namespace PI.UnitaryGroupMassFormula.LCG

namespace DualI

open Formalism.UG Formalism.UG.P

abbrev AA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F

abbrev SS (I : Formalism.MainNotions.S.AutInst) : Subring (AA I) := Formalism.MainNotions.S.IntAf I.F I.E

abbrev iA (I : Formalism.MainNotions.S.AutInst) : I.E →+* AA I := Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)

theorem sig_eq (I : Formalism.MainNotions.S.AutInst) :
    ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := rfl

theorem mem_latSet (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (u : Fin I.n → I.E) :
    u ∈ PI.LatCountG.latSet I y ↔
      (((y.2 : GL (Fin I.n) (AA I))⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
        (fun i => iA I (u i)) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := by
  unfold PI.LatCountG.latSet
  rw [Set.mem_ofPred_eq, PI.UnitaryGroupMassFormula.LSC.LatIs.lamAf_eq I]
  rfl

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (w x : n → A) : hform τ J w (a • x) = a * hform τ J w x := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x + x') = hform τ J w x + hform τ J w x' := by
  unfold hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_sub_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w x x' : n → A) : hform τ J w (x - x') = hform τ J w x - hform τ J w x' := by
  unfold hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (w : n → A) : hform τ J w 0 = 0 := by
  unfold hform
  simp

theorem pair_int (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) (hw : w ∈ I.L)
    (x : Fin I.n → AA I) (hx : x ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L) :
    hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) (fun i => iA I (w i)) x ∈ SS I := by
  have hσ (e : I.E) :
      sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (iA I e) = iA I (starRingEnd I.E e) := by
    rw [← sig_eq I]
    simp [iA, sigR, inclE]
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, hl, rfl⟩ := h
    obtain ⟨b, hb⟩ := (I.L_dual l).mp hl w hw
    have hpair :
        hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I))
          (fun i => iA I (w i)) (fun i => iA I (l i)) =
        iA I (hform (starRingEnd I.E) I.J w l) := by
      simp only [hform, hσ, Matrix.map_apply, map_sum, map_mul]
    rw [hpair, ← hb]
    exact levelaf_tmul_mem b (one_mem (intAd I.F))
  | zero =>
    rw [hform_zero_right]
    exact (SS I).zero_mem
  | add x y _ _ hx hy =>
    rw [hform_add_right]
    exact (SS I).add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, hform_smul_right]
    exact (SS I).mul_mem a.2 hx

end DualI

open DualI Formalism.UG Formalism.UG.P in
theorem dual_lattice_inclusion : DualIncl := by
  intro I y u hu
  let embed (v : Fin I.n → I.E) : Fin I.n → AA I := fun i => iA I (v i)
  let C (a : 𝓞 I.F) : AA I := levelafC I.E a
  let L := latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L
  let σ := sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)
  let J := I.J.map (iA I)
  let g : GL (Fin I.n) (AA I) := y.2
  let G : Matrix (Fin I.n) (Fin I.n) (AA I) := g
  let H : Matrix (Fin I.n) (Fin I.n) (AA I) := (g⁻¹ : GL (Fin I.n) (AA I))
  have hU : cT σ G * J * G = J := y.2.2
  have hGH : G * H = 1 := Units.mul_inv g
  have hHG : H * G = 1 := Units.inv_mul g
  have hmem (v : Fin I.n → I.E) : v ∈ PI.LatCountG.latSet I y ↔ H *ᵥ embed v ∈ L :=
    mem_latSet I y v
  have hC (a : 𝓞 I.F) : iA I (algebraMap (𝓞 I.F) I.E a) = C a := by
    change (algebraMap (𝓞 I.F) I.E a) ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) =
      (1 : I.E) ⊗ₜ[I.F] algebraMap (𝓞 I.F) (Formalism.MainNotions.S.Af I.F) a
    rw [IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E,
      IsScalarTower.algebraMap_apply (𝓞 I.F) I.F (Formalism.MainNotions.S.Af I.F),
      Algebra.algebraMap_eq_smul_one (A := I.E), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
  have hσ (e : I.E) : σ (iA I e) = iA I (starRingEnd I.E e) := by
    rw [← sig_eq I]
    simp [σ, iA, sigR, inclE]
  have hint (e : I.E) (he : IsIntegral ℤ e) : iA I e ∈ SS I :=
    levelaf_tmul_mem (⟨e, he⟩ : 𝓞 I.E) (one_mem (intAd I.F))
  have hσint {a : AA I} (ha : a ∈ SS I) : σ a ∈ SS I := by
    refine (show SS I ≤ (SS I).comap σ from Subring.closure_le.2 ?_) ha
    rintro _ (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · change σ (iA I (algebraMap (𝓞 I.E) I.E b)) ∈ SS I
      rw [hσ]
      exact hint _ ((RingOfIntegers.isIntegral_coe b).map (starRingEnd I.E).toIntAlgHom)
    · change σ ((1 : I.E) ⊗ₜ[I.F] a) ∈ SS I
      simpa [σ, sigR] using levelaf_tmul_mem (E := I.E) 1 ha
  have hpair (v w : Fin I.n → I.E) :
      hform σ J (embed v) (embed w) = iA I (hf I v w) := by
    simp only [hf, hform, J, embed, hσ, Matrix.map_apply, map_sum, map_mul]

  have happ (a : 𝓞 I.F) (ha : a ≠ 0) (s : AA I) (hs : s ∈ SS I) :
      ∃ e : I.E, IsIntegral ℤ e ∧ ∃ t ∈ SS I, s = iA I e + C a * t := by
    refine Subring.closure_induction
      (p := fun s _ => ∃ e : I.E, IsIntegral ℤ e ∧ ∃ t ∈ SS I, s = iA I e + C a * t)
      ?_ ?_ ?_ ?_ ?_ ?_ hs
    · rintro _ (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨q, hq⟩, rfl⟩)
      · exact ⟨_, RingOfIntegers.isIntegral_coe b, 0, zero_mem _, by simp [iA, inclE]⟩
      · obtain ⟨r, t, ht, hqt⟩ := csGlob_intAdApprox I.F a ha q hq
        refine ⟨algebraMap (𝓞 I.F) I.E r, ?_, (1 : I.E) ⊗ₜ[I.F] t, ?_, ?_⟩
        · rw [IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]
          exact (RingOfIntegers.isIntegral_coe r).algebraMap
        · simpa using levelaf_tmul_mem (E := I.E) 1 ht
        · rw [hC]
          simp only [C, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          rw [← TensorProduct.tmul_add, ← hqt]
    · exact ⟨0, isIntegral_zero, 0, zero_mem _, by simp⟩
    · exact ⟨1, isIntegral_one, 0, zero_mem _, by simp⟩
    · rintro s t _ _ ⟨e, he, v, hv, rfl⟩ ⟨f, hf, w, hw, rfl⟩
      exact ⟨e + f, he.add hf, v + w, add_mem hv hw, by rw [map_add]; ring⟩
    · rintro s _ ⟨e, he, v, hv, rfl⟩
      exact ⟨-e, he.neg, -v, neg_mem hv, by rw [map_neg]; ring⟩
    · rintro s t _ _ ⟨e, he, v, hv, rfl⟩ ⟨f, hf, w, hw, rfl⟩
      refine ⟨e * f, he.mul hf, v * iA I f + iA I e * w + C a * v * w, ?_, ?_⟩
      · exact add_mem (add_mem (mul_mem hv (hint f hf)) (mul_mem (hint e he) hw))
          (mul_mem (mul_mem (levelafC_mem a) hv) hw)
      · rw [map_mul]
        ring
  have happrox (a : 𝓞 I.F) (ha : a ≠ 0) (x : Fin I.n → AA I) :
      ∃ v : Fin I.n → I.E, ∃ t : Fin I.n → AA I, (∀ i, t i ∈ SS I) ∧
        x = embed v + (fun i => C a * t i) := by
    have hcoord (i : Fin I.n) : ∃ v : I.E, ∃ t ∈ SS I, x i = iA I v + C a * t := by
      obtain ⟨d, hd, hdx⟩ := levelaf_denom (F := I.F) (x i)
      obtain ⟨e, -, t, ht, hx⟩ := happ (d * a) (mul_ne_zero hd ha) (C d * x i) hdx
      let r := algebraMap (𝓞 I.F) I.E d
      have hr : r ≠ 0 := adelstab_algebraMap_ne_zero d hd
      have hunit : iA I r⁻¹ * C d = 1 := by
        rw [← hC, ← map_mul, inv_mul_cancel₀ hr, map_one]
      refine ⟨r⁻¹ * e, t, ht, ?_⟩
      change C d * x i = iA I e + levelafC I.E (d * a) * t at hx
      rw [levelafC_mul] at hx
      change C d * x i = iA I e + C d * C a * t at hx
      rw [map_mul]
      linear_combination iA I r⁻¹ * hx - x i * hunit + (C a * t) * hunit
    choose v t ht hv using hcoord
    exact ⟨v, t, ht, funext hv⟩

  obtain ⟨m, hm, hsingle⟩ := csGlob_single I.L I.L_span
  let c : 𝓞 I.F := m
  have hc : c ≠ 0 := Int.cast_ne_zero.2 hm
  have hembed_single (i : Fin I.n) (a : I.E) :
      embed (Pi.single i a) = Pi.single i (iA I a) := by
    funext j
    by_cases h : j = i <;> simp [embed, h]
  have hsingle_sum (a : AA I) (t : Fin I.n → AA I) (ht : ∀ i, t i ∈ SS I) :
      (fun i => a * t i) = ∑ k, (⟨t k, ht k⟩ : SS I) • Pi.single k a := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, mul_comm]
    · intro k _ hki
      simp [Ne.symm hki]
    · exact fun hi => (hi (Finset.mem_univ i)).elim
  have hlower (t : Fin I.n → AA I) (ht : ∀ i, t i ∈ SS I) :
      (fun i => C c * t i) ∈ L := by
    rw [hsingle_sum (C c) t ht]
    refine sum_mem fun k _ => L.smul_mem _ ?_
    have hk : Pi.single k (C c) = embed (Pi.single k (m : I.E)) := by
      rw [hembed_single, ← hC, show algebraMap (𝓞 I.F) I.E c = (m : I.E) from map_intCast _ _]
    rw [hk]
    exact Submodule.subset_span ⟨_, hsingle k, rfl⟩

  obtain ⟨d, hd, b, hb, -, M, hM⟩ := levelaf_exists_denom (F := I.F) g
  have hden (i j : Fin I.n) : C d * H i j ∈ SS I := by
    have hij := congrFun (congrFun hM i) j
    change (M i j : AA I) = (b : AA I) * H i j at hij
    rw [← show (b : AA I) = C d from hb, ← hij]
    exact (M i j).2
  have hsmall (t : Fin I.n → AA I) (ht : ∀ i, t i ∈ SS I) :
      H *ᵥ (fun i => C (c * d) * t i) ∈ L := by
    have heq : H *ᵥ (fun i => C (c * d) * t i) =
        fun i => C c * ∑ j, (C d * H i j) * t j := by
      funext i
      simp only [mulVec, dotProduct, C, levelafC_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    exact hlower _ fun i => sum_mem fun j _ => mul_mem (hden i j) (ht j)

  let P := Submodule.span (SS I) (embed '' PI.LatCountG.latSet I y)
  have hspan (w : Fin I.n → AA I) (hw : w ∈ L) : G *ᵥ w ∈ P := by
    obtain ⟨v, t, ht, hv⟩ := happrox (c * d) (mul_ne_zero hc hd) (G *ᵥ w)
    have hvlat : v ∈ PI.LatCountG.latSet I y := by
      rw [hmem, show embed v = G *ᵥ w - (fun i => C (c * d) * t i) from eq_sub_of_add_eq hv.symm,
        mulVec_sub, mulVec_mulVec, hHG, one_mulVec]
      exact sub_mem hw (hsmall t ht)
    have hbasis (k : Fin I.n) : Pi.single k (C (c * d)) ∈ P := by
      let r := algebraMap (𝓞 I.F) I.E (c * d)
      have hr : embed (Pi.single k r) = Pi.single k (C (c * d)) := by
        rw [hembed_single, hC]
      rw [← hr]
      apply Submodule.subset_span
      refine ⟨_, (hmem _).2 ?_, rfl⟩
      have hscale : (fun i => C (c * d) * (Pi.single k 1 : Fin I.n → AA I) i) =
          Pi.single k (C (c * d)) := by
        funext i
        by_cases h : i = k <;> simp [h]
      rw [hr, ← hscale]
      exact hsmall (Pi.single k 1) fun i => by
        by_cases h : i = k <;> simp [h]
    rw [hv, hsingle_sum _ t ht]
    exact add_mem (Submodule.subset_span ⟨v, hvlat, rfl⟩)
      (sum_mem fun k _ => P.smul_mem _ (hbasis k))

  have hleft (w : Fin I.n → AA I) (hw : w ∈ P) : hform σ J w (embed u) ∈ SS I := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, hv, rfl⟩ := hw
      obtain ⟨b, hb⟩ := hu v hv
      rw [hpair, ← hb]
      exact hint _ (RingOfIntegers.isIntegral_coe b)
    | zero =>
      rw [csDual_hform_zero_left]
      exact zero_mem _
    | add w v _ _ hw hv =>
      rw [csDual_hform_add_left]
      exact add_mem hw hv
    | smul a w _ hw =>
      rw [Subring.smul_def, csDual_hform_smul_left]
      exact mul_mem (hσint a.2) hw
  let z := H *ᵥ embed u
  have hz : G *ᵥ z = embed u := by
    rw [show z = H *ᵥ embed u from rfl, mulVec_mulVec, hGH, one_mulVec]
  have hdual (w : Fin I.n → AA I) (hw : w ∈ L) : hform σ J w z ∈ SS I := by
    have h := hleft _ (hspan w hw)
    rwa [← hz, hform_mulVec, hU] at h

  have hdiagonal (e : I.E) (he : iA I e ∈ SS I) : IsIntegral ℤ e := by
    let T : AA I →ₗ[I.F] Formalism.MainNotions.S.Af I.F :=
      (TensorProduct.lid I.F _).toLinearMap ∘ₗ (Algebra.trace I.F I.E).rTensor _
    have hT (x : I.E) (a : Formalism.MainNotions.S.Af I.F) :
        T (x ⊗ₜ[I.F] a) = algebraMap I.F _ (Algebra.trace I.F I.E x) * a := by
      simp only [T, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, Algebra.smul_def]
    have hTint (s : AA I) (hs : s ∈ SS I) : T s ∈ intAd I.F := by
      let B := Module.finBasis ℤ (𝓞 I.E)
      obtain ⟨r, hr, rfl⟩ := levelaf_decomp B (Module.Basis.span_eq B) hs
      rw [map_sum]
      refine sum_mem fun j _ => ?_
      rw [hT]
      obtain ⟨a, ha⟩ := adelstab_trace_int (F := I.F) (B j)
      rw [← ha, ← IsScalarTower.algebraMap_apply]
      exact mul_mem (levelaf_int_mem a) (hr j)
    let N : Submodule (𝓞 I.F) I.E :=
      { carrier := {x | iA I x ∈ SS I}
        add_mem' := fun {x y} hx hy => by
          change iA I (x + y) ∈ SS I
          rw [map_add]
          exact add_mem hx hy
        zero_mem' := by
          change iA I 0 ∈ SS I
          rw [map_zero]
          exact zero_mem _
        smul_mem' := fun a x hx => by
          change iA I (a • x) ∈ SS I
          rw [Algebra.smul_def, map_mul, hC]
          exact mul_mem (levelafC_mem a) hx }
    let β := Module.finBasis I.F I.E
    obtain ⟨q, hq, -, hqint⟩ := sf_den (fun i => β i)
    let β' := (Algebra.traceForm I.F I.E).dualBasis (traceForm_nondegenerate I.F I.E) β
    let W := Submodule.span (𝓞 I.F) (Set.range fun i => q⁻¹ * β' i)
    have hle : N ≤ W := by
      intro x hx
      have htrace (b : 𝓞 I.E) :
          Algebra.trace I.F I.E (x * algebraMap (𝓞 I.E) I.E b) ∈ (algebraMap (𝓞 I.F) I.F).range := by
        have hprod : iA I (x * algebraMap (𝓞 I.E) I.E b) ∈ SS I := by
          rw [map_mul]
          exact mul_mem hx (hint _ (RingOfIntegers.isIntegral_coe b))
        apply adelstab_F_int
        have h := hTint _ hprod
        change T (_ ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) ∈ intAd I.F at h
        rwa [hT, mul_one] at h
      have h := adelstab_dual β q hqint x htrace
      let f := (LinearMap.mulLeft I.F q⁻¹).restrictScalars (𝓞 I.F)
      have hx' := Submodule.mem_map_of_mem (f := f) h
      rw [Submodule.map_span] at hx'
      have hf : f (q * x) = x := by
        change q⁻¹ * (q * x) = x
        rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]
      rw [hf] at hx'
      exact Submodule.span_mono (by rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩) hx'
    have : Module.Finite (𝓞 I.F) W := Module.Finite.span_of_finite _ (Set.finite_range _)
    have : IsNoetherian (𝓞 I.F) W := inferInstance
    have : IsNoetherian (𝓞 I.F) N := isNoetherian_of_le hle
    have hN : N ≠ ⊥ := by
      intro h
      have h1 : (1 : I.E) ∈ N := hint 1 isIntegral_one
      exact one_ne_zero (h ▸ h1 : (1 : I.E) ∈ (⊥ : Submodule (𝓞 I.F) I.E))
    refine isIntegral_trans (R := ℤ) (A := 𝓞 I.F) e
      (isIntegral_of_smul_mem_submodule N hN (Module.Finite.iff_fg.mp inferInstance) e ?_)
    intro x hx
    change iA I (e * x) ∈ SS I
    rw [map_mul]
    exact mul_mem he hx

  obtain ⟨v, t, ht, hv⟩ := happrox c hc z
  have htL : (fun i => C c * t i) ∈ L := hlower t ht
  have hvL : v ∈ I.L := by
    rw [I.L_dual v]
    intro w hw
    have hwL : embed w ∈ L := Submodule.subset_span ⟨w, hw, rfl⟩
    have h : IsIntegral ℤ (hf I w v) := by
      apply hdiagonal
      rw [← hpair, show embed v = z - (fun i => C c * t i) from eq_sub_of_add_eq hv.symm, hform_sub_right]
      exact sub_mem (hdual _ hwL) (pair_int I w hw _ htL)
    exact ⟨⟨_, h⟩, rfl⟩
  apply (hmem u).2
  change z ∈ L
  rw [hv]
  exact add_mem (Submodule.subset_span ⟨v, hvL, rfl⟩) htL

end PI.UnitaryGroupMassFormula.LCG
