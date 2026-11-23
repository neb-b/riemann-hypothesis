module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.SmoothClassInFiniteOrder
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0003
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.GmapLocEqOfFrame
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecayA
section
open Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def CCw (k r : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E) : Prop :=
  SS k r F ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ C


open Classical in
def cstW {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0

theorem cstW_spec {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by
  unfold cstW
  rw [dite_eq_left ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg

def termW {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cstW hF (β.take a) (β.drop a)) 0)

theorem inCC_of_CCw {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (m : ℕ) :
    B.InCC (k := k) (r := r) A m F := by
  obtain ⟨N, e, c, K, hK, he, hc, hcK⟩ := basis_exists k r
  have he' : ∀ i, B.inLie k r (e i) := fun i => (he i).1
  have hgN : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ A := fun g => Real.rpow_nonneg (Real.sqrt_nonneg _) A
  have hterm : ∀ a b, 0 ≤ termW e K hF a b := fun a b =>
    mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)

  have hword : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ termW e K hF u.length v.length := by
    intro u v hu hv g hg
    set ks := List.replicate u.length true ++ List.replicate v.length false with hks
    have hlen : (u ++ v).length = ks.length := by simp [hks]
    have hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K := by
      intro X hX
      have hX' : B.unitLie k r X := by
        rcases List.mem_append.1 hX with h | h
        · exact hu X h
        · exact hv X h
      exact ⟨hX'.1, hcK X hX'⟩
    have hexp := expand e c hK he' hc ks (u ++ v) hlen hxs id good_id F hF.1 g hg
    rw [B.dLR, ← B.dLR, dLR_eq_ev]
    have hl : (u ++ v).length = u.length + v.length := List.length_append
    rw [hl] at hexp
    calc B.gN g ^ A * ‖ev ks (u ++ v) F g‖
        ≤ B.gN g ^ A * (K ^ (u.length + v.length) * bsum e ks (fun β => ‖id (ev ks β F) g‖)) :=
          mul_le_mul_of_nonneg_left hexp (hgN g)
      _ = K ^ (u.length + v.length) * bsum e ks (fun β => B.gN g ^ A * ‖ev ks β F g‖) := by
          rw [bsum_mul]; simp only [id]; ring
      _ ≤ termW e K hF u.length v.length := by
          unfold termW
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)
          refine bsum_mono e ks _ _ ?_
          intro β hβ hβe
          have hβl : β.length = u.length + v.length := by rw [hβ]; simp [hks]
          have h1 : (β.take u.length).length = u.length := by simp [List.length_take, hβl]
          have h2 : (β.drop u.length).length = v.length := by simp [List.length_drop, hβl]
          have hev : ev ks β F = B.dLR (β.take u.length) (β.drop u.length) F := by
            rw [dLR_eq_ev, h1, h2, List.take_append_drop]
          have hunit : ∀ X ∈ β, B.unitLie k r X := by
            intro X hX
            obtain ⟨i, rfl⟩ := hβe X hX
            exact he i
          rw [hev]
          exact (cstW_spec hF _ _ (fun X hX => hunit X (List.mem_of_mem_take hX))
            (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg).trans (le_max_left _ _)
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff'⟩ := hF.1 g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), hff'⟩
  · intro u v hu hv hl g hg
    refine (hword u v hu hv g hg).trans ?_
    have ha : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hb : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc termW e K hF u.length v.length
        ≤ ∑ b ∈ Finset.range (m + 1), termW e K hF u.length b :=
          Finset.single_le_sum (fun b _ => hterm _ b) hb
      _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), termW e K hF a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hterm a b) ha

end Formalism.L2.SG.Pf.CoefDecay
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0

open ReciprocityTheory.ChartRestriction.L3.WA

def SemiGenusLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ x, x ∈ M₁ ↔ g x ∈ M₂

def SemiGenusZLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ {r : ℕ} (s : Fin r → V) (z : V) (M₁ M₂ : AddSubgroup V),
      IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      (∀ a, h (s a) z = 0) →
      (∀ w ∈ Submodule.span K (Set.range s), w ∈ M₁ ↔ w ∈ M₂) →
      (∀ w ∈ M₁, ∃ w₁ ∈ M₁, w₁ ∈ Submodule.span K (Set.range s) ∧ ∀ a, h (s a) (w - w₁) = 0) →
      (∀ w ∈ M₂, ∃ w₁ ∈ M₂, w₁ ∈ Submodule.span K (Set.range s) ∧ ∀ a, h (s a) (w - w₁) = 0) →
      z ∈ M₁ → z ∈ M₂ →
      (∀ c : K, c • z ∈ M₁ → c ∈ locRing p) → (∀ c : K, c • z ∈ M₂ → c ∈ locRing p) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ a, g (s a) = s a) ∧ g z = z ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂

def PrimPlaneLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ (N : AddSubgroup V) (z : V) (b : K), IsSelfDualMod (locRing p) h N → z ∈ N →
      (∀ c : K, c • z ∈ N → c ∈ locRing p) → ¬ IsUnitIn (locRing p) (h z z) →
      b ∈ locRing p → star b = b → (∃ w : V, h z w = 1 ∧ h w w = b) →
      ∃ y ∈ N, h z y = 1 ∧ h y y = b

end Formalism.L2.SG.Pf.LatDictZ.Z0
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
section
noncomputable section

open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.RedConj0Pf

open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin

section

variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))

def ivH : (Fin I.n → I.E) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  AddMonoidHom.mk' (iv I) (DictLat.iv_add I)

theorem ivH_apply (v : Fin I.n → I.E) : ivH I v = iv I v := rfl

def TH (x : I.Gf) : (Fin I.n → I.E ⊗[I.F] Af I.F) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  (Matrix.mulVecLin (I.fmat x)).toAddMonoidHom

theorem TH_apply (x : I.Gf) (v : Fin I.n → I.E ⊗[I.F] Af I.F) : TH I x v = I.fmat x *ᵥ v := rfl

theorem T_mem {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hb : ∀ i, b i ∈ I.L)
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : I.fmat x *ᵥ iv I (b i) ∈ I.Lf := by
  have hsub : Lw I w ≤ I.Lf := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have hyL : y ∈ I.L := by
      refine (Submodule.span_le.mpr ?_) hy
      rintro _ ⟨a, _, z, hz, rfl⟩
      rw [show ((a : 𝓞 I.E) : I.E) • z = a • z from algebraMap_smul I.E a z]
      exact I.L.smul_mem a hz
    exact Submodule.subset_span ⟨⟨y, hyL⟩, rfl⟩
  have hmem : ∀ j, iv I (b j) ∈ I.Lf := fun j => Submodule.subset_span ⟨⟨b j, hb j⟩, rfl⟩
  have hS : (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) ∈ I.Lf :=
    sum_mem (fun j _ => by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hmem j) _)
  have h := add_mem (hsub (hM i)) hS
  rwa [sub_add_cancel] at h

theorem red_eq {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b i)) =
      ∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j)) := by
  have hsum : (∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j))) =
      (Lw I w).mkQ (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [hsum]
  exact (Submodule.Quotient.eq _).mpr (hM i)

theorem zcoef_q (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • (wLat0 I w).mkQ (b l) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  refine zcoef I w p hp hcard hb z ?_ l
  have h : (wLat0 I w).mkQ (∑ l, z l • b l) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simpa only [map_zsmul] using hz
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem zcoef_A (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • (Lw I w).mkQ (iv I (b l)) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  refine zcoef I w p hp hcard hb z ?_ l
  refine mem_wLat0_of_iv I w p hp.pos (p_mem I w p hp hcard) _ ?_
  have h : (Lw I w).mkQ (ivH I (∑ l, z l • b l)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]; simpa only [map_zsmul, ivH_apply] using hz
  exact (Submodule.Quotient.mk_eq_zero _).1 h

end

theorem reduction_conjugacy : Formalism.L2.SG.Pf.RowDictPf.RedConj0 := by
  intro I w p hp hcard m hm x M M' hM hM'
  subst hm
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hb, hMb0⟩ := hM
  obtain ⟨b', hb', hMb0'⟩ := hM'
  have hMb : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) :
      I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w := hMb0
  have hMb' : ∀ i, I.fmat x *ᵥ iv I (b' i) - ∑ j, ((((M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) :
      I.E ⊗[I.F] Af I.F) • iv I (b' j) ∈ Lw I w := hMb0'

  choose C hC using fun i => hb.2 (b' i) (hb'.1 i)
  choose D hD using fun i => hb'.2 (b i) (hb.1 i)
  let CM : Matrix (Fin I.n) (Fin I.n) ℤ := Matrix.of fun k i => C i k
  let DM : Matrix (Fin I.n) (Fin I.n) ℤ := Matrix.of fun k i => D i k
  let Mz : Matrix (Fin I.n) (Fin I.n) ℤ :=
    Matrix.of fun j i => ((((M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) : ℤ)
  let M'z : Matrix (Fin I.n) (Fin I.n) ℤ :=
    Matrix.of fun j i => ((((M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) : ℤ)
  have hCz : ∀ i, b' i - ∑ k, CM k i • b k ∈ wLat0 I w := fun i => by
    simpa only [CM, Matrix.of_apply, Int.cast_smul_eq_zsmul] using hC i
  have hDz : ∀ i, b i - ∑ k, DM k i • b' k ∈ wLat0 I w := fun i => by
    simpa only [DM, Matrix.of_apply, Int.cast_smul_eq_zsmul] using hD i

  have hqC : ∀ i, (wLat0 I w).mkQ (b' i) = ∑ k, CM k i • (wLat0 I w).mkQ (b k) := fun i => by
    have h1 : (wLat0 I w).mkQ (b' i) = (wLat0 I w).mkQ (∑ k, CM k i • b k) :=
      (Submodule.Quotient.eq _).2 (hCz i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]; simp only [map_zsmul]
  have hqD : ∀ i, (wLat0 I w).mkQ (b i) = ∑ k, DM k i • (wLat0 I w).mkQ (b' k) := fun i => by
    have h1 : (wLat0 I w).mkQ (b i) = (wLat0 I w).mkQ (∑ k, DM k i • b' k) :=
      (Submodule.Quotient.eq _).2 (hDz i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]; simp only [map_zsmul]
  have hCDz : ∀ l i, ((((1 : Matrix (Fin I.n) (Fin I.n) ℤ) - CM * DM) l i : ℤ) : ZMod p) = 0 := by
    intro l i
    refine zcoef_q I w p hp hcard hb (fun l => ((1 : Matrix (Fin I.n) (Fin I.n) ℤ) - CM * DM) l i) ?_ l
    have h2 : (wLat0 I w).mkQ (b i) = ∑ l, (CM * DM) l i • (wLat0 I w).mkQ (b l) := by
      rw [hqD i]; simp only [hqC]; exact comb _ CM DM i
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← h2, sub_self]

  have hTb : ∀ j, I.fmat x *ᵥ iv I (b j) ∈ I.Lf := T_mem I w hb.1 hMb
  have hTb' : ∀ j, I.fmat x *ᵥ iv I (b' j) ∈ I.Lf := T_mem I w hb'.1 hMb'
  have hTexp : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) =
      I.fmat x *ᵥ iv I (b' i) - ∑ k, CM k i • (I.fmat x *ᵥ iv I (b k)) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← TH_apply I x, ← ivH_apply I, map_sub, map_sub, map_sum, map_sum]
    simp only [map_zsmul, ivH_apply, TH_apply]
  have hTeL : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) ∈ I.Lf := fun i => by
    rw [hTexp]
    exact sub_mem (hTb' i) (Submodule.sum_mem _ fun k _ => zsmul_mem (hTb k) _)
  obtain ⟨r, hr1, hrL⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup I.L_fg le_rfl (span_of_red I w hb)
  have hTe : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) ∈ Lw I w := fun i => by
    set e := b' i - ∑ k, CM k i • b k with he_def
    have he : e ∈ wLat0 I w := hCz i
    have hre : r • e ∈ Submodule.span (𝓞 I.E) (Set.range b) :=
      hrL (Submodule.smul_mem_pointwise_smul _ r I.L (wLat0_le I w he))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hre
    have hcw : ∀ j, c j ∈ w.asIdeal := indep I w hb.1 (span_of_red I w hb) c
      (by rw [hc, ← wLat0_eq]; exact (wLat0 I w).smul_mem r he)
    have h1 : Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) • (I.fmat x *ᵥ iv I e) ∈ Lw I w := by
      have e3 : Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) • (I.fmat x *ᵥ iv I e) =
          ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (c j : I.E) • (I.fmat x *ᵥ iv I (b j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Matrix.mulVec_smul, ← DictLat.iv_smulO, ← hc, ← TH_apply I x, ← ivH_apply I, map_sum, map_sum]
        simp only [ivH_apply, DictLat.iv_smulO, TH_apply, Matrix.mulVec_smul]
      rw [e3]
      exact Submodule.sum_mem _ fun j _ => smul_mem_Lw I w (hcw j) (hTb j)
    have h2 := smul_mem_Lw I w hr1 (hTeL i)
    have e4 : Formalism.UG.inclE (F := I.F) (Af I.F) (((r - 1 : 𝓞 I.E)) : I.E) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) - 1 := by
      rw [sub_eq_add_neg, DictRing.incl_add, DictRing.incl_neg, DictRing.incl_one, ← sub_eq_add_neg]
    rw [e4, sub_smul, one_smul] at h2
    have h3 := sub_mem h1 h2
    rwa [sub_sub_cancel] at h3

  have hqA' : ∀ j, (Lw I w).mkQ (iv I (b' j)) = ∑ l, CM l j • (Lw I w).mkQ (iv I (b l)) := fun j => by
    have h0 : iv I (b' j) - ∑ l, CM l j • iv I (b l) ∈ Lw I w := by
      have := iv_mem_Lw I w (hCz j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← ivH_apply I, map_sub, map_sum] at this
      simpa only [map_zsmul, ivH_apply] using this
    have h1 : (Lw I w).mkQ (iv I (b' j)) = (Lw I w).mkQ (∑ l, CM l j • iv I (b l)) :=
      (Submodule.Quotient.eq _).2 h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]; simp only [map_zsmul]
  have hA : ∀ i, (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i)) =
      ∑ l, (CM * M'z) l i • (Lw I w).mkQ (iv I (b l)) := fun i => by
    rw [red_eq I w hMb' i]; simp only [hqA']
    exact comb (fun l => (Lw I w).mkQ (iv I (b l))) CM M'z i
  have hB : ∀ i, (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i)) =
      ∑ l, (Mz * CM) l i • (Lw I w).mkQ (iv I (b l)) := fun i => by
    have h0 : I.fmat x *ᵥ iv I (b' i) =
        I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) + ∑ k, CM k i • (I.fmat x *ᵥ iv I (b k)) := by
      rw [hTexp, sub_add_cancel]
    have hz : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (hTe i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_add (f := _), hz, zero_add, map_sum]
    simp only [map_zsmul, red_eq I w hMb]
    exact comb (fun l => (Lw I w).mkQ (iv I (b l))) Mz CM i
  have hMCz : ∀ l i, (((Mz * CM - CM * M'z) l i : ℤ) : ZMod p) = 0 := by
    intro l i
    refine zcoef_A I w p hp hcard hb (fun l => (Mz * CM - CM * M'z) l i) ?_ l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← hA i, ← hB i, sub_self]

  let φ := (Int.castRingHom (ZMod p)).mapMatrix (m := Fin I.n)
  have hφ0 : ∀ X : Matrix (Fin I.n) (Fin I.n) ℤ, (∀ l i, ((X l i : ℤ) : ZMod p) = 0) → φ X = 0 := by
    intro X hX; ext l i
    simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom, Matrix.zero_apply]
    exact hX l i
  have hCD : φ CM * φ DM = 1 := by
    have h := hφ0 _ hCDz
    rw [map_sub, map_one, map_mul, sub_eq_zero] at h
    exact h.symm
  have hDC : φ DM * φ CM = 1 := mul_eq_one_comm.1 hCD
  have hMC : φ Mz * φ CM = φ CM * φ M'z := by
    have h := hφ0 _ hMCz
    rwa [map_sub, map_mul, map_mul, sub_eq_zero] at h
  have hMz : φ Mz = (M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) := by
    ext j i
    simp only [φ, Mz, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have hM'z : φ M'z = (M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) := by
    ext j i
    simp only [φ, M'z, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hMz, hM'z] at hMC
  refine ⟨⟨φ CM, φ DM, hCD, hDC⟩, Units.ext ?_⟩
  show (M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) = φ DM * (M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) * φ CM
  rw [mul_assoc, hMC, ← mul_assoc, hDC, one_mul]

end Formalism.L2.SG.Pf.RedConj0Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionExists
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix

namespace Formalism.L2.SG.Pf.RedExists0Pf

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf

theorem reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RedExists0 := by
  intro I w p hp hcard m hm x hx
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hb⟩ := exists_redBasis I w hp hcard
  have hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  have hxi : x⁻¹ ∈ I.Kset := (Formalism.UG.stabGL I.Lf).inv_mem hx
  have hxi' : ∀ v, v ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ v ∈ I.Lf := hxi
  choose c hc using fun i => coords I w hp hcard hb ((hx' _).1 (DictLat.iv_mem I (hb.1 i)))
  choose c' hc' using fun i => coords I w hp hcard hb ((hxi' _).1 (DictLat.iv_mem I (hb.1 i)))
  let M : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun j i => ((c i j : ℤ) : ZMod p)
  let N : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun k j => ((c' j k : ℤ) : ZMod p)
  have hzs : ∀ (z : ℤ) {v : Fin I.n → I.E ⊗[I.F] Af I.F}, v ∈ lamAf (F := I.F) (wLat0 I w) →
      (z : I.E ⊗[I.F] Af I.F) • v ∈ lamAf (F := I.F) (wLat0 I w) := fun z v hv => by
    rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hv z
  have hdiv : ∀ i k, (p : ℤ) ∣ (1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k := by
    intro i
    have hW : iv I (b i) - ∑ j, (c i j : I.E ⊗[I.F] Af I.F) •
        ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ lamAf (F := I.F) (wLat0 I w) := by
      have h1 := stab_w I w hxi (hc i)
      have h2 : ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ iv I (b j) -
          ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k)) ∈ lamAf (F := I.F) (wLat0 I w) :=
        Submodule.sum_mem _ fun j _ => hzs _ (hc' j)
      have h3 := Submodule.add_mem _ h1 h2
      convert h3 using 1
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hW2 : iv I (b i - ∑ k, ((∑ j, c i j * c' j k : ℤ) : I.E) • b k) ∈
        lamAf (F := I.F) (wLat0 I w) := by
      rw [iv_lin]
      convert hW using 2
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [← Finset.sum_smul, Int.cast_sum, Int.cast_mul]
    have h4 := inter I w hW2
    intro k
    have h5 : ∑ k, (((1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k : ℤ) : I.E) • b k ∈
        wLat0 I w := by
      convert h4 using 1
      simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    exact redBasis_indep I w hp hcard hb _ h5 k
  have hNM : N * M = 1 := by
    ext k i
    have h := hdiv i k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    push_cast at h
    rw [sub_eq_zero] at h
    simp only [N, M, Matrix.mul_apply, Matrix.of_apply]
    have e : ∑ j, ((c' j k : ℤ) : ZMod p) * ((c i j : ℤ) : ZMod p) =
        ∑ j, ((c i j : ℤ) : ZMod p) * ((c' j k : ℤ) : ZMod p) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e, ← h]
    by_cases hik : i = k
    · subst hik; simp
    · simp [Matrix.one_apply_ne hik, Matrix.one_apply_ne (Ne.symm hik)]
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  refine ⟨⟨M, N, hMN, hNM⟩, b, hb, fun i => ?_⟩
  show I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M j i).val : ℕ)) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈
    lamAf (F := I.F) (wLat0 I w)
  have hS : (∑ j, ((((((c i j : ℤ) : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ((c i j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j))) ∈ lamAf (F := I.F) (wLat0 I w) :=
    Submodule.sum_mem _ fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have key := Submodule.sub_mem _ (hc i) hS
  convert key using 1
  simp only [M, Matrix.of_apply, Finset.sum_sub_distrib]
  abel

end Formalism.L2.SG.Pf.RedExists0Pf
end
end

