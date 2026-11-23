module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0001
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RingHom.Etale

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRootHensPf
section
noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

theorem hens_isUnit_of_mk {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x : B)
    (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := (Ideal.Quotient.mk_surjective (hx.unit⁻¹ : (B ⧸ J)ˣ).1)
  have h1 : Ideal.Quotient.mk J (x * y) = Ideal.Quotient.mk J 1 := by
    rw [map_mul, hy, map_one]; exact hx.mul_val_inv
  have h2 : x * y - 1 ∈ J := Ideal.Quotient.eq.mp h1
  have h3 : IsUnit (x * y) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ h2)
  exact isUnit_of_mul_isUnit_left h3

theorem hens_isUnit_of_sub {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x y : B)
    (hxy : x - y ∈ J) (hy : IsUnit (Ideal.Quotient.mk J y)) : IsUnit x := by
  apply hens_isUnit_of_mk J hJ
  have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.mpr hxy
  rwa [this]

theorem hens_eval_sub_mem {B : Type} [CommRing B] (J : Ideal B) (p : B[X]) (x y : B) (h : x - y ∈ J) :
    p.eval x - p.eval y ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub x y p
  rw [hk]; exact J.mul_mem_right k h

theorem hens_q_eval {A : Type} [CommRing A] (f : A[X]) (a : A) (hf : f.Monic) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h : C (f.eval a) + (X - C a) * (f /ₘ (X - C a)) = f := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval]; exact Polynomial.modByMonic_add_div f _
  conv_rhs => rw [← h]
  simp [derivative_mul]

theorem LeafRootHens_of : LeafRootHens := by
  intro A B _ _ I J hJ ψ hIJ f a hf hfa hu
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson_bot]
    exact hJ.jac
  have hmk : ∀ x : A, IsUnit (Ideal.Quotient.mk I x) → IsUnit (Ideal.Quotient.mk J (ψ x)) := by
    intro x hx
    have := hx.map (Ideal.quotientMap J ψ hIJ)
    simpa [Ideal.quotientMap_mk] using this
  have hder : ∀ z : B, (f.map ψ).derivative.eval z = (f.derivative.map ψ).eval z := by
    intro z; rw [Polynomial.derivative_map]
  have e0 : ∀ (p : A[X]), (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
    intro p; rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hev0 : (f.map ψ).eval (ψ a) ∈ J := by rw [e0]; exact hIJ hfa
  have hu0 : IsUnit (Ideal.Quotient.mk J ((f.map ψ).derivative.eval (ψ a))) := by
    rw [hder, e0]; exact hmk _ hu
  obtain ⟨c, hc, hca⟩ := hJ.is_henselian (f.map ψ) (hf.map ψ) (ψ a) hev0 hu0
  have hc1 : IsUnit ((f.derivative.map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  have hc2 : IsUnit (((f /ₘ (X - C a)).map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← hens_q_eval f a hf, ← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  refine ⟨c, hc, hca, hc1, hc2, ?_⟩
  intro c' hc' hc'a
  have hd : c' - c ∈ J := by
    have := J.sub_mem hc'a hca
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map ψ) c (c' - c)
  rw [add_sub_cancel, hc'.eq_zero, hc.eq_zero, zero_add] at hk
  have hfac : (c' - c) * ((f.map ψ).derivative.eval c + k * (c' - c)) = 0 := by
    rw [hk]; ring
  have hunit : IsUnit ((f.map ψ).derivative.eval c + k * (c' - c)) := by
    apply hens_isUnit_of_sub J hjac _ ((f.map ψ).derivative.eval c)
    · rw [add_sub_cancel_left]; exact J.mul_mem_left k hd
    · rw [hder]; exact hc1.map _
  have : c' - c = 0 := (hunit.mul_left_eq_zero).mp hfac
  exact sub_eq_zero.mp this

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRootStdPf
section
noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

lemma std_decomp {A : Type} [CommRing A] (f : A[X]) (a : A) :
    f = (X - C a) * (f /ₘ (X - C a)) + C (f.eval a) := by
  have h := modByMonic_add_div f (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  rw [add_comm]; exact h.symm

lemma std_eval {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (f : A[X]) (a : A) (c : B) :
    (f.map ψ).eval c = (c - ψ a) * ((f /ₘ (X - C a)).map ψ).eval c + ψ (f.eval a) := by
  conv_lhs => rw [std_decomp f a]
  simp [Polynomial.map_mul, Polynomial.map_sub]

lemma std_deriv {A : Type} [CommRing A] (f : A[X]) (a : A) :
    f.derivative.eval a = (f /ₘ (X - C a)).eval a := by
  have h : f.derivative.eval a = (derivative ((X - C a) * (f /ₘ (X - C a)) + C (f.eval a))).eval a :=
    congrArg (fun p => (derivative p).eval a) (std_decomp f a)
  rw [h]; simp [derivative_mul]

lemma aeval_eq_eval_map {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (p : A[X]) (x : B) :
    aeval x p = (p.map (algebraMap A B)).eval x := by
  rw [aeval_def, eval_map]

theorem LeafRootStd_of : LeafRootStd := by
  intro A _ I f a hf hfa hu
  set q := f /ₘ (X - C a) with hq
  let P : StandardEtalePair A := ⟨f, hf, f.derivative * q, ⟨q, 0, 1, by ring⟩⟩
  set φ := algebraMap A P.Ring with hφ
  have hX := P.hasMap_X
  have hroot : (f.map φ).eval P.X = 0 := by
    rw [← aeval_eq_eval_map]; exact hX.1
  have hgunit : IsUnit ((f.derivative.map φ).eval P.X * (q.map φ).eval P.X) := by
    have h2 := hX.2
    change IsUnit (aeval P.X (f.derivative * q)) at h2
    rwa [map_mul, aeval_eq_eval_map, aeval_eq_eval_map] at h2
  have hqunit : IsUnit ((q.map φ).eval P.X) := isUnit_of_mul_isUnit_right hgunit
  have hba : P.X - φ a ∈ I.map φ := by
    have e := std_eval φ f a P.X
    rw [hroot] at e
    have e2 : (P.X - φ a) * (q.map φ).eval P.X = -φ (f.eval a) := by linear_combination -e
    obtain ⟨u, hu'⟩ := hqunit
    rw [← hu'] at e2
    have e3 : P.X - φ a = ((P.X - φ a) * u) * ↑u⁻¹ := by simp [mul_assoc]
    rw [e3, e2]
    exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.mem_map_of_mem _ hfa))
  have hmk : ∀ p : A[X], aeval (Ideal.Quotient.mk I a) p = Ideal.Quotient.mk I (p.eval a) := by
    intro p
    rw [← Ideal.Quotient.algebraMap_eq]
    exact aeval_algebraMap_apply_eq_algebraMap_eval a p
  have hga : IsUnit (Ideal.Quotient.mk I ((f.derivative * q).eval a)) := by
    rw [eval_mul, ← std_deriv, map_mul]; exact hu.mul hu
  have hm : P.HasMap (Ideal.Quotient.mk I a) := by
    refine ⟨?_, ?_⟩
    · change aeval _ f = 0
      rw [hmk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    · change IsUnit (aeval _ (f.derivative * q))
      rw [hmk]; exact hga
  refine ⟨P.Ring, inferInstance, φ, P.X, (RingHom.etale_algebraMap).mpr inferInstance,
    ⟨(P.lift _ hm : P.Ring →+* A ⧸ I),
      (AlgHom.comp_algebraMap (P.lift _ hm)).trans (Ideal.Quotient.algebraMap_eq I)⟩,
    ?_, hroot, hba, ?_, ?_⟩
  ·
    set J := I.map φ with hJ
    let π := Ideal.Quotient.mk J
    let R' := (π.comp φ).range
    have hXm : π P.X ∈ R' := ⟨a, (Ideal.Quotient.eq.mpr hba).symm⟩

    obtain ⟨v, hv⟩ := hga
    obtain ⟨u, hu2⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)
    have hgu : ((f.derivative * q).eval a) * u - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, map_one, ← hv, hu2]; simp
    have hgb : π (aeval P.X P.g) = π (φ ((f.derivative * q).eval a)) := by
      apply Ideal.Quotient.eq.mpr
      change aeval P.X (f.derivative * q) - _ ∈ J
      rw [aeval_eq_eval_map, ← hφ]
      have hd := sub_dvd_eval_sub P.X (φ a) ((f.derivative * q).map φ)
      have hev : ((f.derivative * q).map φ).eval (φ a) = φ ((f.derivative * q).eval a) := by
        rw [eval_map, eval₂_at_apply]
      rw [hev] at hd
      obtain ⟨w, hw⟩ := hd
      rw [hw]; exact Ideal.mul_mem_right _ _ hba
    let mkP : A[X][X] →+* P.Ring := Ideal.Quotient.mk (Ideal.span {C P.f, X * C P.g - 1})
    have hY : π (mkP X) ∈ R' := by
      refine ⟨u, ?_⟩
      have h1 : aeval P.X P.g * mkP X = 1 := P.aeval_X_g_mul_mk_X
      have e1 : π (aeval P.X P.g) * π (mkP X) = 1 := by rw [← map_mul, h1, map_one]
      have h3 : π (φ ((f.derivative * q).eval a)) * π (φ u) = 1 := by
        rw [← map_mul, ← map_mul, ← map_one π, ← map_one φ]
        exact Ideal.Quotient.eq.mpr (by rw [← map_sub]; exact Ideal.mem_map_of_mem _ hgu)
      change π (φ u) = _
      linear_combination (-π (φ u)) * e1 + (π (mkP X) * π (φ u)) * hgb + π (mkP X) * h3
    have hin : ∀ c : A[X], π (mkP (C c)) ∈ R' := by
      intro c
      refine Polynomial.induction_on c (fun a0 => ⟨a0, rfl⟩) ?_ ?_
      · intro p1 p2 h1 h2; rw [C_add, map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
      · intro n a0 ih
        rw [pow_succ, ← mul_assoc, C_mul, map_mul, map_mul]; exact mul_mem ih hXm
    have hall : ∀ p : A[X][X], π (mkP p) ∈ R' := by
      intro p
      refine Polynomial.induction_on p hin ?_ ?_
      · intro p1 p2 h1 h2; rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
      · intro n a0 ih
        rw [pow_succ, ← mul_assoc, map_mul, map_mul]; exact mul_mem ih hY
    intro s
    obtain ⟨p, rfl⟩ : ∃ p, mkP p = s := Ideal.Quotient.mk_surjective s
    obtain ⟨a', ha'⟩ := hall p
    exact ⟨a', Ideal.Quotient.eq.mp ha'.symm⟩
  · intro B _ χ₁ χ₂ h hb
    letI : Algebra A B := (χ₁.comp φ).toAlgebra
    let e₁ : P.Ring →ₐ[A] B := ⟨χ₁, fun _ => rfl⟩
    let e₂ : P.Ring →ₐ[A] B := ⟨χ₂, fun r => (congrArg (fun g : A →+* B => g r) h).symm⟩
    have := StandardEtalePair.hom_ext (f := e₁) (g := e₂) hb
    ext s
    exact congrArg (fun e : P.Ring →ₐ[A] B => e s) this
  · intro B _ ψ c hc h1 h2
    letI : Algebra A B := ψ.toAlgebra
    have hm' : P.HasMap c := by
      refine ⟨?_, ?_⟩
      · change aeval c f = 0
        rw [aeval_eq_eval_map]; exact hc
      · change IsUnit (aeval c (f.derivative * q))
        rw [map_mul, aeval_eq_eval_map, aeval_eq_eval_map]; exact h1.mul h2
    exact ⟨(P.lift c hm' : P.Ring →+* B), AlgHom.comp_algebraMap (P.lift c hm'), P.lift_X c hm'⟩

end LateralTheory.CohomologicalPurity.Hz
end
end

