module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure
section
open MeasureTheory

namespace GlobalTheory.Cusp.Shear

theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
section
namespace GlobalTheory.UnitaryChar

section Mat

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : ℕ}

theorem root {S A : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_std {S U : Matrix (Fin n) (Fin n) ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix (Fin n) (Fin n) ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem polar {G s u : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.IndefR.Datum.IsCartanInv G s) (hu : uᴴ * G * u = G) :
    ∃ k q : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G ∧ s * k = k * s ∧ qᴴ * G * q = G ∧ s * q * s * q = 1 ∧
      u = k * q * q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hG : Gᴴ = G := by
    have e : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul, h3.isHermitian.eq]
    have e1 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← Matrix.one_mul Gᴴ, ← e1, Matrix.mul_assoc, e, ← Matrix.mul_assoc, h2]
  obtain ⟨B, hB, hBB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, Bᴴ = B ∧ B * B = G * s :=
    ⟨CFC.sqrt (G * s), (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self _ h3.posSemidef.nonneg⟩
  have hd : IsUnit B.det := by
    have : IsUnit (B * B).det := by rw [hBB]; exact (Matrix.isUnit_iff_isUnit_det _).1 h3.isUnit
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨C, hC, i1, i2⟩ : ∃ C : Matrix (Fin n) (Fin n) ℂ, Cᴴ = C ∧ B * C = 1 ∧ C * B = 1 :=
    ⟨B⁻¹, by rw [Matrix.conjTranspose_nonsing_inv, hB], Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩
  have j1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, B * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, C * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  obtain ⟨S, hs, hGS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, s = C * S * B ∧ G = B * S * B :=
    ⟨B * s * C, by simp only [Matrix.mul_assoc, j2, i2, Matrix.mul_one], by
      simp only [Matrix.mul_assoc, i2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hBB, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  have hS : S = C * G * C := by rw [hGS]; simp only [Matrix.mul_assoc, j2, i1, Matrix.mul_one]
  have s1 : S * S = 1 := by
    have := congrArg (fun X => B * X * C) h1
    simpa only [hs, Matrix.mul_assoc, j1, i1, Matrix.mul_one] using this
  have s2 : Sᴴ = S := by
    rw [hS]; simp only [Matrix.conjTranspose_mul, hC, hG, Matrix.mul_assoc]
  have tr : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * S * X = S → (C * X * B)ᴴ * G * (C * X * B) = G := fun X hX => by
    calc _ = B * (Xᴴ * S * X) * B := by
          rw [hGS]; simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc, j1, j2]
      _ = G := by rw [hX, hGS]
  obtain ⟨K, Q, k1, k2, q1, q2, e⟩ := polar_std (U := B * u * C) s1 s2 (by
    calc _ = C * (uᴴ * (B * S * B) * u) * C := by
          simp only [Matrix.conjTranspose_mul, hC, hB, Matrix.mul_assoc]
      _ = S := by rw [← hGS, hu, ← hS])
  refine ⟨C * K * B, C * Q * B, tr K k1, ?_, tr Q q1, ?_, ?_⟩
  · have := congrArg (fun X => C * X * B) k2
    simpa only [hs, Matrix.mul_assoc, j1] using this
  · have := congrArg (fun X => C * X * B) q2
    simpa only [hs, Matrix.mul_assoc, j1, Matrix.one_mul, i2] using this
  · have := congrArg (fun X => C * X * B) e
    simpa only [Matrix.mul_assoc, j1, j2, i2, Matrix.mul_one] using this

end Mat

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem compAt_mt_mul {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) (g g' : GA D W) :
    compAt θ τ (Formalism.L2.Theta.mt W (g * g')) =
      compAt θ τ (Formalism.L2.Theta.mt W g) * compAt θ τ (Formalism.L2.Theta.mt W g') :=
  Matrix.map_mul (L := Formalism.L2.Theta.mt W g) (M := Formalism.L2.Theta.mt W g') (f := (θ τ).comp (infPart D))

theorem compAt_mt_one {D : D7} (θ : InfFam D) (W : HSp D) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 :=
  Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem ext_real {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g g' : GA D W} (hg : g ∈ GinfC W)
    (hg' : g' ∈ GinfC W) (h : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = compAt θ τ (Formalism.L2.Theta.mt W g')) :
    g = g' := by
  refine mul_inv_eq_one.1 ((GlobalTheory.UnitarySplit.real_finite_split D W).2.2.1 _ (mul_mem hg (inv_mem hg'))
    ((GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun τ => ?_))
  show compAt θ τ (Formalism.L2.Theta.mt W (g * g'⁻¹)) = 1
  rw [compAt_mt_mul, h, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]

theorem char_eq_one : ∀ (D : D7) (θ : InfFam D) (W : HSp D), IsInfFam θ → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ c : GA D W → ℂ, (∀ u ∈ GinfC W, ∀ u' ∈ GinfC W, c (u * u') = c u * c u') → (∀ u ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W u) = compAt θ τ (Formalism.L2.Theta.mt W u) * s τ) → c u = 1) → ∀ u ∈ GinfC W, c u = 1 := by
  intro D θ W hθ s hs c hm hK u hu
  have gl : ∀ x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, (x τ)ᴴ * gramAt D W τ * x τ = gramAt D W τ) →
      ∃ g ∈ GinfC W, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W g) = x τ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ W).2
  choose k q k1 k2 q1 q2 e using fun τ => polar (u := compAt θ τ (Formalism.L2.Theta.mt W u)) (hs τ)
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u τ)
  obtain ⟨k', hk, ek⟩ := gl k k1
  obtain ⟨q', hq, eq⟩ := gl q q1
  obtain ⟨σ, hσ, eσ⟩ := gl s fun τ => (hs τ).2.1
  have ck : c k' = 1 := hK _ hk fun τ => by rw [ek, k2]
  have cσ : c σ = 1 := hK _ hσ fun τ => by rw [eσ]
  have c1 : c 1 = 1 := hK _ (one_mem _) fun τ => by rw [compAt_mt_one, Matrix.mul_one, Matrix.one_mul]
  have e1 : u = k' * q' * q' := ext_real hθ W hu (mul_mem (mul_mem hk hq) hq) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, ek, eq, e]
  have e2 : σ * q' * σ * q' = 1 := ext_real hθ W (mul_mem (mul_mem (mul_mem hσ hq) hσ) hq) (one_mem _) fun τ => by
    rw [compAt_mt_mul, compAt_mt_mul, compAt_mt_mul, eσ, eq, q2, compAt_mt_one]
  rw [← e2, hm _ (mul_mem (mul_mem hσ hq) hσ) _ hq, hm _ (mul_mem hσ hq) _ hσ, hm _ hσ _ hq, cσ, one_mul,
    mul_one] at c1
  rw [e1, hm _ (mul_mem hk hq) _ hq, hm _ hk _ hq, ck, one_mul, c1]

end GlobalTheory.UnitaryChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinGen

open GlobalTheory.LatVac GlobalTheory.LatFinMod

theorem pair_smul_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (α : Af F) (x : E) :
    algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α) * (pairA F 0 1 ⊗ₜ[F] x) = pairA F 0 α ⊗ₜ[F] x := by
  have hp : pairA F 0 α * pairA F 0 1 = pairA F 0 α := Prod.ext (mul_zero _) (mul_one _)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact congrArg (· ⊗ₜ[F] x) hp

theorem smul_finTens_one {D : D7} {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • finTens 1 M = finTens α M :=
  Matrix.ext fun i j => pair_smul_tmul α (M i j)

theorem latO_finitely_generated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  intro D S T ΛS ΛT hS hT
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS.1.fg
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT.1.fg
  refine ⟨finTens 1 '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)),
    ((hA.prod (hB.prod hC)).image _).image _, ?_, fun U hU u hu => ?_⟩
  · rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨1, fun v => ?_, fun v hv => absurd trivial hv,
      a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    rw [map_one]; exact one_mem _
  · refine (AddSubgroup.closure_le U).2 ?_ hu
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
      (AddMonoidHom.mk' (finTens α) (finTens_add α)).toIntLinearMap
    have hle : Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) ≤
        U.toIntSubmodule.comap φ := by
      refine Submodule.span_le.2 fun M hM => ?_
      have := hU α hα _ ⟨M, hM, rfl⟩
      rw [smul_finTens_one] at this
      exact this
    exact hle (genMap_mem_span S T (hA2 _ ha) (hB2 _ hs) (hC2 _ ht))

end GlobalTheory.LatFinGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviRestriction
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def contLeft : Submodule ℂ (Sm E a) where
  carrier := {f | Continuous f.1 ∧ ∀ γ g, f.1 (ratGL E a γ * g) = f.1 g}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl⟩
  add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun γ g => by
    change f.1 _ + h.1 _ = f.1 _ + h.1 _
    rw [hf.2, hh.2]⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun γ g => by
    change c • f.1 _ = c • f.1 _
    rw [hf.2]⟩

theorem span_cpt_le_contLeft {φ : Sm E a} (hA : IsAutForm φ) :
    Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ≤ contLeft E a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  have hc := ContAut.continuous_of_isOpen_stab E a φ hA.level
  refine ⟨hc.comp (continuous_mul_const _), fun γ g => ?_⟩
  change φ.1 (ratGL E a γ * g * _) = φ.1 (g * _)
  rw [mul_assoc, hA.left]

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

def sliceLin (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] {𝓕 : Set (BlockIx a r → Ad E)}
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (hr : r ≤ a) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) : contLeft E a →ₗ[ℂ] (GA E (a - r) → ℂ) where
  toFun f := slice E μ 𝓕 hr f.1.1 m₁ t κ
  map_add' f h := by
    funext m₂
    exact integral_add (CuspidalL2GL.integrableOn_unip f.2.1 f.2.2 μ h𝓕 _) (CuspidalL2GL.integrableOn_unip h.2.1 h.2.2 μ h𝓕 _)
  map_smul' c f := by
    funext m₂
    exact integral_const_mul c _

theorem slice_kfin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)),
      ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 _ φ hA m₁ t κ ψ hψ
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hV
  have hfin : FiniteDimensional ℂ V := hA.kfin
  have hle := span_cpt_le_contLeft hA
  let L : V →ₗ[ℂ] (GA E (a - r) → ℂ) := sliceLin μ h𝓕 hr m₁ t κ ∘ₗ Submodule.inclusion hle
  have hR : FiniteDimensional ℂ (LinearMap.range L) := inferInstance
  set S := Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)
  have hS : S.map (Sm E (a - r)).subtype ≤ LinearMap.range L := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨cptRep E a (κ⁻¹ * blkK hr k * κ) φ, Submodule.subset_span ⟨_, rfl⟩⟩, ?_⟩
    funext g
    change slice E μ 𝓕 hr (cptRep E a (κ⁻¹ * blkK hr k * κ) φ).1 m₁ t κ g =
      ψ.1 (g * infGL E (a - r) (Unitary.toUnits k))
    rw [hψ, slice_mul_cpt]
    unfold slice
    congr 1
    funext x
    change φ.1 (_ * _ * _) = _
    simp only [mul_assoc]
    rfl
  have h1 : FiniteDimensional ℂ (S.map (Sm E (a - r)).subtype) := Submodule.finiteDimensional_of_le hS
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (Sm E (a - r)).subtype Subtype.val_injective S).symm

end GlobalTheory.SliceTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalUnipotentVanishing
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_unipotent_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π → ∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → ∀ w : V, w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  first | exact @GlobalTheory.SmGL.CuspSpan.mem_span_unip | exact GlobalTheory.SmGL.CuspSpan.mem_span_unip | (intros; apply GlobalTheory.SmGL.CuspSpan.mem_span_unip <;> assumption)
end

