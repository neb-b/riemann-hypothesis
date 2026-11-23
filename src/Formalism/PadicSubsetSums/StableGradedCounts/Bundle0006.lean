module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Lemmata.FirstBlockLemmaG.Imports
public import Lemmata.MiscLemmasA.Imports
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0003
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0005

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.BaseChangeIwahoriFactorization
section
namespace Formalism.IrreducibleCountingLemmas.Z

theorem isUnit_sub_of_mem_maximalIdeal {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  first | exact Bl.FirstBlockLemmaG.goal1 .. | (apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha hm | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O

theorem iwahori_factorization_exists (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  first | exact Bl.SecondBlockLemmaB.goal1 .. | (apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.CentralIdempotentsSumOne
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

namespace CISum

open Classical in
theorem centralIdem_act {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  have := hρ.1
  have := hσ.1
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ.2
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ.2
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc
  have e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g := by
    unfold centralIdem
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
    rfl
  obtain ⟨μ, hμ⟩ := schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by
    intro g k
    have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    simp only [this, Representation.char_conj])
  have htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹ := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring
  have horth := Representation.char_orthonormal σ ρ
  rw [Nat.card_eq_fintype_card] at horth
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  rw [e, hμ]
  split_ifs with hiso
  · rw [if_pos hiso] at horth
    obtain ⟨φ⟩ := hiso
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ) := by
      field_simp at horth
      simpa using horth
    rw [hsum, hc, hdim, div_mul_cancel₀ _ hc0] at htr
    have : μ = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, one_smul]
  · rw [if_neg hiso] at horth
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc0] using horth
    rw [hsum, mul_zero] at htr
    rw [(mul_eq_zero.mp htr).resolve_right hd, zero_smul]

theorem isIrr_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by
  unfold Representation.IsIrreducible at h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
    · left
      exact congrArg Subrepresentation.toSubmodule h1
    · right
      exact congrArg Subrepresentation.toSubmodule h1

end CISum

open CISum in
set_option backward.isDefEq.respectTransparency false in
theorem central_idempotents_sum_one : CentralIdemSumOne := by
  intro G I _ _ _ V _ _ _ ρ hirr hne hfull
  classical
  set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz
  have hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z := by
    intro x
    rw [hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hirr i).1
    exact (central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x

  have hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1 := by
    intro W _ _ _ σ hσ
    obtain ⟨i₀, φ, hφ⟩ := hfull W σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum, Finset.sum_eq_single i₀]
    · rw [centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]
      exact ⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩
    · intro i _ hi
      rw [centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]
      rintro ⟨ψ⟩
      apply hi
      apply hne
      refine ⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩
      have h1 : ψ (ρ i g x) = σ g (ψ x) := LinearMap.congr_fun (ψ.isIntertwining' g) x
      simp only [LinearEquiv.trans_apply]
      erw [h1]
      exact hφ g _
    · intro h; exact absurd (Finset.mem_univ _) h
  have : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  let N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {x | z * x = x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_add, hx, hy]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc, hcentral a, mul_assoc, hx] }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)]
    apply sSup_le
    intro S hS x hx
    have hS' : IsSimpleModule (MonoidAlgebra ℂ G) S := hS
    have hirrS := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'
    have hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) := by
      let ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G :=
        { toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) :
            MonoidAlgebra ℂ G)
          map_add' := by intro a b; simp
          map_smul' := by
            intro c y
            simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
      refine Module.Finite.of_injective ι ?_
      intro a b hab
      exact (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)
    have h1 := hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)
    have h2 := LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    have h3 := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2
    have h4 : z * x = x := by simpa using congrArg Subtype.val h3
    exact h4
  have h1 : (1 : MonoidAlgebra ℂ G) ∈ N := hN ▸ Submodule.mem_top
  have h2 : z * 1 = 1 := h1
  rwa [mul_one] at h2

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit
section
open scoped NumberField

namespace Formalism.IrreducibleCountingLemmas.Z

theorem degree_one_split : DegreeOneSplit := by
  intro F E _ _ _ _ _ h2 P _ hP hf he
  classical
  set p : Ideal (𝓞 F) := P.under (𝓞 F) with hp
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : P.inertiaDeg (𝓞 F) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨inferInstance, ⟨rfl⟩⟩
  have hpos : ∀ q : p.primesOver (𝓞 E), 1 ≤ q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := by
    intro q
    have : q.1.IsPrime := q.2.1
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := 𝓞 F) q.1) (Ideal.inertiaDeg_pos q.1 (𝓞 F))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨P, hPmem⟩ : p.primesOver (𝓞 E)))] at hsum
  simp only [he, hf1, mul_one] at hsum
  have hrest : ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 1 := by omega
  have hle : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≤ 1 := by
    calc _ = ∑ q ∈ Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E)), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => hpos q
      _ = 1 := hrest
  have hge : (Finset.univ.erase (⟨P, hPmem⟩ : p.primesOver (𝓞 E))).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hrest
    simp at hrest
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hle hge
  have key : Fintype.card { x // x ∈ p.primesOver (𝓞 E) } = 2 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact key

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero
section
open Polynomial
open scoped TensorProduct

namespace Formalism.IrreducibleCountingLemmas.Z

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  classical
  by_contra hcon
  have hinj : Function.Injective (aeval g p) := by
    refine (injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_
    by_contra hw0
    exact hcon ⟨w, hw0, hw⟩
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hunit : IsUnit (aeval g p) := by
    first
      | exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
      | exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hunitL := hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)
  have hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)
      = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) := by
    rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0 := by
    rw [Polynomial.eval_map, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]
  rw [← hE] at h0
  have hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)) := by
    first
      | exact ((Module.End.isUnit_iff _).1 hunitL).1
      | exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)
  exact hv.2 (hbij (h0.trans (map_zero _).symm))

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  classical
  have hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x) := fun _ _ _ => rfl
  have hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x := fun _ _ _ => rfl
  have hone : ∀ x : V, (1 : Module.End K V) x = x := fun _ => rfl
  have hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0 := by
    intro s t x hx
    rw [map_mul, hm, hx, map_zero]
  have hsq : Squarefree g.charpoly := hs.squarefree
  refine WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero
  · intro u hu _
    exact ⟨0, map_zero _, fun q _ => hu.dvd⟩
  · intro a i _ hi ih hdvd
    have ha : a ∣ g.charpoly := dvd_of_mul_left_dvd hdvd
    have hid : i ∣ g.charpoly := dvd_of_mul_right_dvd hdvd
    obtain ⟨ea, hea0, hea⟩ := ih ha
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g i hi hid
    have hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n := fun n h => by
      first
        | exact (Irreducible.coprime_iff_not_dvd hi).2 h
        | exact (Irreducible.isCoprime_iff_not_dvd hi).2 h
    have hcop : IsCoprime i a := hcopOf a fun hia =>
      hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))
    refine ⟨ea + w, ?_, fun q hq => ?_⟩
    · rw [map_add (f := _), hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]
    · have hw' : aeval g (i * q) w = 0 := by
        rw [mul_comm]
        exact hkill i q w hw
      have hqi : aeval g (i * q) ea = 0 := by
        have h1 := hkill q i _ hq
        rwa [map_add, hw', add_zero] at h1
      have haq : a ∣ q := by
        have h2 : a ∣ i * q := hea _ hqi
        first
          | exact hcop.symm.dvd_of_dvd_mul_left h2
          | exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
      have hea' : aeval g (a * q) ea = 0 := by
        rw [mul_comm]
        exact hkill a q ea hea0
      have hwq : aeval g (a * q) w = 0 := by
        have h1 := hkill q a _ hq
        rwa [map_add, hea', zero_add] at h1
      have hiaq : i ∣ a * q := by
        by_contra hn
        obtain ⟨u, t, hut⟩ := hcopOf _ hn
        apply hw0
        have h2 : aeval g (u * i + t * (a * q)) w = 0 := by
          rw [map_add (f := _), hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]
        rwa [hut, map_one, hone] at h2
      have hiq : i ∣ q := by
        first
          | exact hcop.dvd_of_dvd_mul_left hiaq
          | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)
      exact hcop.mul_dvd hiq haq

theorem base_change_cyclic_vector : BCCyclicVector := by
  unfold BCCyclicVector
  intro K V _ _ _ _ g hs
  classical
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  let φ : K[X] →ₗ[K] V :=
    { toFun := fun q => aeval g q e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V :=
    φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype
  have hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero,
      LinearMap.charpoly_natDegree]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    have hmem := Polynomial.mem_degreeLT.1 x.2
    have hd : g.charpoly ∣ x.1 := he x.1 hx
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))
  haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm
  have hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  refine ⟨e, fun v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj v
  exact ⟨x.1, hx⟩

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
  obtain ⟨ι, B, hB⟩ := exists_isTranscendenceBasis' (algebraicClosure F E) E
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis B hB
  let e₁ : MvPolynomial ι (algebraicClosure F E) ≃ₐ[algebraicClosure F E]
      Algebra.adjoin (algebraicClosure F E) (Set.range B) := hB.1.aevalEquiv
  let m : MvPolynomial ι (algebraicClosure F E) ≃+* MvPolynomial ι (algebraicClosure F E) :=
    MvPolynomial.mapEquiv ι σ₀.toRingEquiv
  let e : Algebra.adjoin (algebraicClosure F E) (Set.range B) ≃+*
      Algebra.adjoin (algebraicClosure F E) (Set.range B) :=
    e₁.symm.toRingEquiv.trans (m.trans e₁.toRingEquiv)
  let σ : E ≃+* E := IsAlgClosure.equivOfEquiv E E e
  have he : ∀ a : algebraicClosure F E,
      e (algebraMap _ _ a) = algebraMap _ _ (σ₀ a) := by
    intro a
    simp only [e, m, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have hσ : ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by
    intro a
    have h1 : (a : E) = algebraMap (Algebra.adjoin (algebraicClosure F E) (Set.range B)) E
        (algebraMap _ _ a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) ?_, hσ⟩
  intro r
  have h1 : algebraMap F E r = ((algebraMap F (algebraicClosure F E) r : algebraicClosure F E) : E) :=
    rfl
  rw [h1, hσ, AlgEquiv.commutes]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemOrthogonal
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbSum
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem prime_cycle_probability_sum : CycleProbSum := cycleProbSum_of_cycleProbPrime prime_cycle_probability

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWCutOperator
section
namespace Formalism.IrreducibleCountingLemmas.TW

theorem asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]
  rfl

end Formalism.IrreducibleCountingLemmas.TW
end

