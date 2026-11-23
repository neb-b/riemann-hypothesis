module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idemAt_eq_split {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
  have key : ∀ f : AE D, Formalism.L2.NTheta.IsIdemAt f P → f = e₀ := by
    intro f hf
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 f hf.1.1 hf.1.2.1 (below_of_idemAt hf) with h | h
    · exact h
    exfalso
    exact hP (conj_of_cA he₀ hf h)
  rw [key e he, key e' he']

theorem idem_orth {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : P ≠ Q) : e * e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : e' * phiE (belowPl Q) 1 = e' := by rw [← hs', mul_add, he'.1.1, he'.1.2.1, add_zero]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · exfalso
      apply hPQ
      apply HeightOneSpectrum.ext
      ext x
      by_cases hx0 : x = 0
      · subst hx0; simp only [zero_mem]
      rw [he.2 x hx0, he'.2 x hx0, h0, h]
    · rw [h, h0]; exact he₀.1.2.1
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (e' * phiE (belowPl Q) 1) = e * e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem idem_orth_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : ¬ Lev.IsConjPl (D := D) P Q) :
    e * cA D e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : cA D e' * phiE (belowPl Q) 1 = cA D e' := by
    rw [← hs', mul_add, mul_comm (cA D e') e', he'.1.2.1, zero_add, ← map_mul, he'.1.1]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · rw [h, h0]; exact he₀.1.2.1
    · exfalso
      exact hPQ (conj_of_cA he he' (h.trans (congrArg (cA D) h0.symm)))
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (cA D e' * phiE (belowPl Q) 1) =
        e * cA D e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem not_two_primes {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpI : (p : 𝓞 D.host.E) ∈ I) (hqI : (q : 𝓞 D.host.E) ∈ I) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)

theorem nat_mem_of_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : Lev.IsConjPl (D := D) P Q) {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨c, hc, hce⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    show (c : D.host.E) = ((n : 𝓞 D.host.E) : D.host.E)
    rw [hce]; push_cast; exact star_natCast n
  rwa [← this]

theorem char_mem {P : HeightOneSpectrum (𝓞 D.host.E)} {q : ℕ} (hq : q.Prime)
    (hc : Nat.card (Formalism.L2.DIV.kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  have hfin : Finite (Formalism.L2.DIV.kP P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  have h0 : (Nat.card (Formalism.L2.DIV.kP P)) • (1 : Formalism.L2.DIV.kP P) = 0 := card_nsmul_eq_zero'
  rw [hc, nsmul_one] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h0

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
section
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nsmul_mem_cpt' {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  let U : X → Set X := fun y => (fun x => x - y) ⁻¹' (H : Set X)
  have hU : ∀ y, IsOpen (U y) := fun y => hH.preimage (continuous_id.sub continuous_const)
  have hcov : K ⊆ ⋃ y ∈ K, U y := fun x hx => Set.mem_biUnion hx (by simp [U, H.zero_mem])
  obtain ⟨t, -, htf, hcov'⟩ := hK.elim_finite_subcover_image (fun y _ => hU y) hcov
  obtain ⟨t', rfl⟩ : ∃ t' : Finset X, (t' : Set X) = t := ⟨htf.toFinset, by simp⟩
  refine ⟨t'.card.factorial, Nat.factorial_pos _, fun y hy => ?_⟩
  have hmaps : ∀ j ∈ Finset.range (t'.card + 1), ∃ i ∈ t', j • y ∈ U i := fun j _ => by
    have := hcov' (hKs y hy j)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hji⟩ := this
    exact ⟨i, by simpa using hi, hji⟩
  choose! f hf using hmaps
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t'.card + 1)) (t := t') (by simp) (f := f) (fun j hj => (hf j hj).1)
  have h1 := (hf j1 hj1).2
  have h2 := (hf j2 hj2).2
  rw [heq] at h1
  have hdiff : ((j1 : ℤ) - j2) • y ∈ H := by
    convert H.sub_mem h1 h2 using 1
    show _ = (j1 • y - f j2) - (j2 • y - f j2)
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
    abel
  have hj1' : j1 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj1)
  have hj2' : j2 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj2)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : ((j2 - j1 : ℕ) : ℤ) • y ∈ H := by
      have := H.neg_mem hdiff
      rw [← neg_zsmul, neg_sub] at this
      rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj2')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c
  · have hk : ((j1 - j2 : ℕ) : ℤ) • y ∈ H := by rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj1')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c

def LatLevel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      ∃ k : ℕ, 0 < k ∧ ∀ u ∈ latAll S T ΛS ΛT, heisO ψ S T (k • u) f = f

theorem latAll_inf (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {u : WO S T} (hu : u ∈ latAll S T ΛS ΛT) :
    u.map (infPart D) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hx
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | zero => ext i j; simp
  | add x y _ _ hx hy =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [(infPart D).map_add, h1, h2, add_zero]
  | neg x _ hx =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [(infPart D).map_neg, h1, neg_zero]

theorem latLevel_of (hL : LatSelfDual D) : LatLevel D := by
  intro ψ hψ S T ΛS ΛT hS hT f hf
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨hcpt, -, -, -⟩ := hL ψ hψ S T ΛS ΛT hS hT
  obtain ⟨m, hm, hmU⟩ := exists_nsmul_mem_cpt' _ hcpt (fun y hy n => AddSubgroup.nsmul_mem _ hy n) U hUo
  refine ⟨m, hm, fun u hu => hU _ (hmU u hu) ?_⟩
  have h0 := latAll_inf S T ΛS ΛT hu
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun h0 i) j
  show infPart D ((m • u) i j) = 0
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h1, mul_zero]

end Formalism.IndefR.Fin

end
end

