module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenericProjClosureDim

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

def tWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (tWeight K) b (pointConeMap R z f) =
      pointConeMap R z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 : IsWeightedHomogeneous (tWeight K) (pointConeMap R z (monomial d a))
        (Finsupp.weight (blockWeight ι) d) := by
      rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
        Finsupp.sum]
      refine IsWeightedHomogeneous.C_mul ?_ _
      refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
      exact ((isWeightedHomogeneous_X (R := L) (tWeight K) p.1).C_mul (z p)).pow (d p)
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι R)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem isMultiProjPrime_pointIdeal (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (R := R) z b f
    rw [hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap R z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

theorem exists_ne_zero_of_span {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by
  by_contra! h0
  have hall : ∀ l, ψ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have := Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i))
      (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])
    simpa using this i
  have htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥ := by
    rw [← hψ, Submodule.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  have hc : e.coord ⟨0, hN⟩ = 0 := by
    have : e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E)) := htop ▸ Submodule.mem_top
    simpa using this
  have := congrArg (fun f => f (e ⟨0, hN⟩)) hc
  simp at this

end GenericProjClosureDim


open GenericProjClosureDim in
theorem GenericProjClosureDim.proof (hDim : DvrConeDimTrdeg.Statement) (hTr : PairBundleTrdeg.Statement) :
    GenericProjClosureDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k)
    · exact exists_ne_zero_of_span hN e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)
    · exact exists_ne_zero_of_span hN e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)
    · exact ⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  refine ⟨hP, hnt, ?_⟩

  have hdy := hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  rw [hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty,
    ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
    show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]
  norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HsymmShiftProof

open NumericalSegreProof

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [Fintype K] [DecidableEq K] in
theorem length_rootList {n : ℕ} (x : Fin n → K → ℤ) (α : Fin n → ℕ) :
    (rootList x α).length = ∑ i, α i := by
  unfold rootList
  simp [List.length_flatMap, Fin.sum_univ_def]

theorem cons_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F W ((c + c') :: l) = intNumL F W (c :: l) + intNumL F W (c' :: l) := by
  have key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get := by
    intro e
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd
    ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

theorem replicate_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W)
    (z s : K → ℤ) : ∀ (n : ℕ) (L : List (K → ℤ)),
    FieldNumbers.relDim W = ((n + L.length : ℕ) : WithBot (WithTop ℤ)) →
    intNumL F W (List.replicate n (z + s) ++ L) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) *
        intNumL F W (List.replicate (n - k) z ++ List.replicate k s ++ L)
  | 0, L, _ => by simp
  | n + 1, L, hd => by
    have hd' : ∀ c : K → ℤ,
        FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by
      intro c
      rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rw [List.replicate_succ, List.cons_append,
      cons_add W hW _ (by rw [hd, List.length_append, List.length_replicate]; congr 1; omega) z s,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s))).symm,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s)) (a := s)).symm,
      replicate_add W hW z s n (z :: L) (hd' z), replicate_add W hW z s n (s :: L) (hd' s),
      ProjectiveBundleNumbers.sum_choose_succ n (fun k => intNumL F W (List.replicate (n + 1 - k) z ++ List.replicate k s ++ L))]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1
      refine intNumL_perm F W ?_
      rw [show n + 1 - k = (n - k) + 1 by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ List.perm_middle
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [show n + 1 - (k + 1) = n - k by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

def H (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ) (L : List (K → ℤ)) : ℤ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple n c, intNumL F W (rootList x α ++ L)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_zero (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (L : List (K → ℤ)) :
    H W x 0 L = intNumL F W L := by
  simp [H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_one (W : Ideal (MRing ι F)) (x : Fin 1 → K → ℤ) (c : ℕ) (L : List (K → ℤ)) :
    H W x c L = intNumL F W (List.replicate c (x 0) ++ L) := by
  unfold H
  rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]
  simp [rootList]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_perm (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ)
    {L L' : List (K → ℤ)} (h : L.Perm L') : H W x c L = H W x c L' :=
  Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)

theorem H_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) {n : ℕ} (x : Fin n → K → ℤ)
    (c : ℕ) (L : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((c + 1 + L.length : ℕ) : WithBot (WithTop ℤ))) (a b : K → ℤ) :
    H W x c ((a + b) :: L) = H W x c (a :: L) + H W x c (b :: L) := by
  unfold H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlen : (rootList x α).length = c := by
    rw [length_rootList]
    exact Finset.Nat.mem_antidiagonalTuple.mp hα
  rw [intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]
  exact cons_add W hW _
    (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_succ (W : Ideal (MRing ι F)) {i : ℕ} (x : Fin (i + 1) → K → ℤ) (c : ℕ)
    (L : List (K → ℤ)) :
    H W x (c + 1) L = H W (fun j => x (Fin.castSucc j)) (c + 1) L + H W x c (x (Fin.last i) :: L) := by
  unfold H
  rw [sum_antidiagonalTuple_succ]
  congr 1
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [rootList_snoc_zero]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [rootList_update_last, List.append_assoc, List.singleton_append]

theorem sum_choose_pascal (M r : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((M + 1).choose k : ℤ) * f k =
      ∑ k ∈ Finset.range (r + 1 + 1), (M.choose k : ℤ) * f k +
        ∑ k ∈ Finset.range (r + 1), (M.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

theorem main (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (s : K → ℤ) :
    ∀ (N : ℕ) (x : Fin (N + 1) → K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
    FieldNumbers.relDim W = ((r + Y.length : ℕ) : WithBot (WithTop ℤ)) →
    H W (fun i => x i + s) r Y =
      ∑ k ∈ Finset.range (r + 1), ((N + r).choose k : ℤ) * H W x (r - k) (List.replicate k s ++ Y)
  | 0, x, r, Y, hd => by
    rw [H_one, replicate_add W hW (x 0) s r Y hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r]
  | N + 1, x, r, Y, hd => by
    induction r generalizing Y with
    | zero => simp [H_zero]
    | succ r ih =>
      have e1 := main W hW s N (fun j => x (Fin.castSucc j)) (r + 1) Y hd
      have e2 := ih (x (Fin.last (N + 1)) :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have e3 := ih (s :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have hadd := H_add W hW (fun i => x i + s) r Y hd (x (Fin.last (N + 1))) s
      have hAB : ∑ k ∈ Finset.range (r + 1 + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - k) (List.replicate k s ++ Y) =
          ∑ k ∈ Finset.range (r + 1 + 1), ((N + (r + 1)).choose k : ℤ) *
              H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y) +
            ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
              H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y) := by
        rw [show N + (r + 1) = N + 1 + r by omega, Finset.sum_range_succ,
          Finset.sum_range_succ (fun k => ((N + 1 + r).choose k : ℤ) *
            H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y)),
          Nat.sub_self, H_zero, H_zero,
          add_right_comm _ _ (∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y)),
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, H_succ W x (r - k) (List.replicate k s ++ Y),
          ← mul_add, H_perm W x (r - k) (List.perm_middle (l₁ := List.replicate k s)).symm]
      have hC : ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - (k + 1)) (List.replicate (k + 1) s ++ Y) =
          ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ s :: Y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_add_right, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [H_succ W (fun i => x i + s) r Y]
      beta_reduce at e1 ⊢
      rw [e1, hadd, e2, e3, show N + 1 + (r + 1) = N + 1 + r + 1 by omega,
        sum_choose_pascal (N + 1 + r) r (fun k => H W x (r + 1 - k) (List.replicate k s ++ Y)), hAB, hC]
      ring

end HsymmShiftProof

theorem HsymmShift.proof : HsymmShift.Statement.{u} := by
  intro F _ K _ _ ι _ W hW d hd N hN x s r Y hrY
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])
  simp only [HsymmShiftProof.H] at h
  rw [h, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.append_assoc]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PairBundleTrdeg.proof (hadd : AdjoinTrdegAdd.Statement) (hind : PairConeLinesIndep.Statement)
    (halg : PairConeAlg.Statement) : PairBundleTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (pairProjCoord y e φ φ' t p) * X p.1
  let x : Fin N ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O (pairProjCoord y e φ φ' t))).trdeg_eq
    have e2 : (pointConeMap O (pairProjCoord y e φ φ' t)).range = Algebra.adjoin O (Set.range gZ) :=
      aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range x ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  have hind' := hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let f : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    f.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) x :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin N ⊕ Unit) x hxZ
    hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open Classical in
def SegreFlagCutDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
      IsMultiHomog s cs → IsMultiHomog h ch →
      (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
      s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
      aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
      ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
        ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W = if 0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k) then 1 else 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

