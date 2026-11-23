module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace NumericalSegreProof

section Combinatorics

theorem sum_antidiagonalTuple_succ {A : Type*} [AddCommMonoid A] (i c : ℕ)
    (f : (Fin (i + 1) → ℕ) → A) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple (i + 1) (c + 1), f α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple i (c + 1), f (Fin.snoc α 0) +
        ∑ β ∈ Finset.Nat.antidiagonalTuple (i + 1) c,
          f (Function.update β (Fin.last i) (β (Fin.last i) + 1)) := by
  have hsum : ∀ (α : Fin (i + 1) → ℕ) (v : ℕ),
      ∑ j, Function.update α (Fin.last i) v j = ∑ j : Fin i, α (Fin.castSucc j) + v := by
    intro α v
    rw [Fin.sum_univ_castSucc]
    simp
  have hsum' : ∀ α : Fin (i + 1) → ℕ,
      ∑ j, α j = ∑ j : Fin i, α (Fin.castSucc j) + α (Fin.last i) := fun α =>
    Fin.sum_univ_castSucc α
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun α : Fin (i + 1) → ℕ => α (Fin.last i) = 0)]
  congr 1
  · refine Finset.sum_nbij' Fin.init (fun α => Fin.snoc α 0) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum'] at hα
      simpa [Fin.init, hα.2] using hα.1
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      refine ⟨?_, by simp⟩
      rw [hsum']
      simpa using hα
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
    · intro α _
      exact Fin.init_snoc _ _
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
  · have linv : ∀ α : Fin (i + 1) → ℕ, α (Fin.last i) ≠ 0 →
        Function.update (Function.update α (Fin.last i) (α (Fin.last i) - 1)) (Fin.last i)
          (Function.update α (Fin.last i) (α (Fin.last i) - 1) (Fin.last i) + 1) = α := by
      intro α hα
      rw [Function.update_self, Function.update_idem, Nat.sub_add_cancel (Nat.pos_of_ne_zero hα),
        Function.update_eq_self]
    refine Finset.sum_nbij' (fun α => Function.update α (Fin.last i) (α (Fin.last i) - 1))
      (fun β => Function.update β (Fin.last i) (β (Fin.last i) + 1)) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum]
      rw [hsum'] at hα
      omega
    · intro β hβ
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      rw [hsum, Function.update_self]
      rw [hsum'] at hβ
      refine ⟨by omega, by omega⟩
    · intro α hα
      simp only [Finset.mem_filter] at hα
      exact linv α hα.2
    · intro β _
      simp
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [linv α hα.2]

end Combinatorics

section Lists

variable {K : Type*} [DecidableEq K]


omit [DecidableEq K] in
theorem rootList_succ {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin (i + 1) → ℕ) :
    rootList x α = rootList (fun j => x (Fin.castSucc j)) (Fin.init α) ++
      List.replicate (α (Fin.last i)) (x (Fin.last i)) := by
  unfold rootList
  rw [List.finRange_succ_last]
  simp [List.flatMap_append, Fin.init, List.flatMap_map]

omit [DecidableEq K] in
theorem rootList_snoc_zero {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin i → ℕ) :
    rootList x (Fin.snoc α 0) = rootList (fun j => x (Fin.castSucc j)) α := by
  rw [rootList_succ, Fin.init_snoc, Fin.snoc_last]
  simp

omit [DecidableEq K] in
theorem rootList_update_last {i : ℕ} (x : Fin (i + 1) → K → ℤ) (β : Fin (i + 1) → ℕ) :
    rootList x (Function.update β (Fin.last i) (β (Fin.last i) + 1)) =
      rootList x β ++ [x (Fin.last i)] := by
  have hinit : Fin.init (Function.update β (Fin.last i) (β (Fin.last i) + 1)) = Fin.init β := by
    funext j
    simp [Fin.init]
  rw [rootList_succ, rootList_succ x β, hinit, Function.update_self, List.replicate_succ',
    List.append_assoc]

omit [DecidableEq K] in
theorem rootList_zero {n : ℕ} (x : Fin n → K → ℤ) : rootList x 0 = [] := by
  simp [rootList]

theorem intNumL_eq {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    (l : List (K → ℤ)) : intNumL F P l = eventualValue (l.foldr diffStep (hilbFn P)) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem intNumL_perm {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    {l l' : List (K → ℤ)} (h : l.Perm l') : intNumL F P l = intNumL F P l' := by
  rw [intNumL_eq, intNumL_eq, h.foldr_eq]

end Lists

def segreSide {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (x : Fin i → K → ℤ) (n : ℕ) (Y : List (K → ℤ)) : ℤ :=
  if i - 1 ≤ n then
    ∑ α ∈ Finset.Nat.antidiagonalTuple i (n - (i - 1)), intNumL F P (rootList x α ++ Y)
  else 0

theorem segreSide_succ {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (hi : 1 ≤ i) (x : Fin (i + 1) → K → ℤ) (m : ℕ)
    (Y : List (K → ℤ)) :
    segreSide F P x (m + 1) Y =
      segreSide F P (fun j => x (Fin.castSucc j)) m Y +
        segreSide F P x m (x (Fin.last i) :: Y) := by
  unfold segreSide
  simp only [Nat.add_sub_cancel]
  by_cases h : i ≤ m + 1
  · obtain ⟨c, hc⟩ : ∃ c, m + 1 = i + c := ⟨m + 1 - i, by omega⟩
    rw [ite_eq_left h, ite_eq_left (by omega), show m + 1 - i = c by omega,
      show m - (i - 1) = c by omega]
    rcases c with _ | c
    · rw [ite_eq_right (by omega), add_zero, Finset.Nat.antidiagonalTuple_zero_right,
        Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Finset.sum_singleton,
        rootList_zero, rootList_zero]
    · rw [ite_eq_left (by omega), show m - i = c by omega, sum_antidiagonalTuple_succ]
      congr 1
      · refine Finset.sum_congr rfl fun α _ => ?_
        rw [rootList_snoc_zero]
      · refine Finset.sum_congr rfl fun β _ => ?_
        rw [rootList_update_last, List.append_assoc, List.singleton_append]
  · rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

theorem zetaDeg_split {K : Type*} (a c : K → ℤ) :
    ((zetaDeg + liftDeg (c - a)) + liftDeg (a - c) : Option K → ℤ) = zetaDeg := by
  funext o
  cases o <;> simp [zetaDeg, liftDeg]

theorem truncCoord_of_le {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) {i : ℕ} (h : N ≤ i) :
    truncCoord t i = t := by
  funext j
  simp [truncCoord, lt_of_lt_of_le j.isLt h]

theorem intNumL_cons_add (hadd : FieldNumbers.IntNumAdd.Statement.{0}) (F : Type) [Field F]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F P ((c + c') :: l) = intNumL F P (c :: l) + intNumL F P (c' :: l) := by
  have key : ∀ d, Function.update (c :: l).get (0 : Fin (l.length + 1)) d = (d :: l).get := by
    intro d
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := hadd F K ι P hP.multiHomog hP.relevant (l.length + 1) hd ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

end NumericalSegreProof


open NumericalSegreProof in
theorem NumericalSegre.proof (hadd : FieldNumbers.IntNumAdd.Statement.{0})
    (hdim : FlagBundleDim.Statement) (hcut : FlagBundleCut.Statement)
    (hvan : FlagBundlePullbackVanish.Statement) (hbase : FlagBundleLineBase.Statement) :
    NumericalSegre.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP hdimV N hN E _ _ B w b hflag M a φ hφ Φ _ _ t ht n Y hnY
  have claim : ∀ i : ℕ, 1 ≤ i → ∀ hi : i ≤ N, ∀ (n : ℕ) (Y : List (K → ℤ)),
      n + Y.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        segreSide F (pointIdeal F y) (fun j : Fin i => a - b (Fin.castLE hi j)) n Y := by
    intro i hi1
    induction i, hi1 using Nat.le_induction with
    | base =>
      intro hi n Y hnY
      rw [hbase F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht hi n Y (by omega)]
      simp [segreSide, Finset.Nat.antidiagonalTuple_one, rootList, List.finRange_succ]
      rfl
    | succ i hi1 ih =>
      intro hi n
      induction n with
      | zero =>
        intro Y hY
        rw [List.replicate_zero, List.nil_append,
          hvan F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1) (by omega) hi Y
            (by omega)]
        unfold segreSide
        rw [ite_eq_right (by omega)]
      | succ m ihm =>
        intro Y hY
        set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
        have hlen : l.length + 1 = e + i := by
          simp [hl]
          omega
        obtain ⟨hPi, hdi⟩ := hdim F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1)
          (by omega) hi
        rw [show e + (i + 1) - 1 = l.length + 1 by omega] at hdi
        rw [List.replicate_succ, List.cons_append, ← hl,
          ← zetaDeg_split a (b ⟨i, hi⟩), intNumL_cons_add hadd F _ hPi l hdi]
        have hc := hcut F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht ⟨i, hi⟩ hi1 l hlen
        simp only at hc
        rw [hc, ih (by omega) m Y (by omega)]
        have hperm : (liftDeg (a - b ⟨i, hi⟩) :: l).Perm
            (List.replicate m zetaDeg ++ ((a - b ⟨i, hi⟩) :: Y).map liftDeg) := by
          rw [hl, List.map_cons]
          exact List.perm_middle.symm
        rw [intNumL_perm F _ hperm, ihm _ (by simp; omega), segreSide_succ F _ hi1]
        rfl
  rw [← truncCoord_of_le t (le_refl N), claim N hN (le_refl N) n Y (by omega)]
  rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord fnField)

section Proof

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type}


omit [Fintype K] in
theorem BirationalJoin.segre_ratio_mem_fnField (y : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (c₁ c₂ : ∀ k, ι₂ k) : segreVec w c₁ / segreVec w c₂ ∈ fnField O (joinCoord y w) := by
  unfold segreVec
  rw [← Finset.prod_div_distrib]
  refine Subfield.prod_mem _ fun k _ => ?_
  apply Subfield.subset_closure
  refine Or.inr ⟨⟨Sum.inr k, c₁ k, c₂ k⟩, rfl⟩

theorem BirationalJoin.segreVec_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K)
    (i : ι k) :
    segreVec y (Function.update c k i) = y ⟨k, i⟩ * ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ := by
  unfold segreVec
  have hf : (fun l => y ⟨l, Function.update c k i l⟩) =
      Function.update (fun l => y ⟨l, c l⟩) k (y ⟨k, i⟩) := by
    funext l
    by_cases hl : l = k
    · subst hl
      simp
    · simp [Function.update_of_ne hl]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ k)]

theorem BirationalJoin.fnField_le_closure_chartRing (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) :
    fnField O y ≤ Subfield.closure (chartRing O (segreVec y) c : Set Ω) := by
  classical
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have hk : y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
    set P := ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ with hP
    have hcP : segreVec y c = y ⟨k, c k⟩ * P := by
      have h := BirationalJoin.segreVec_update y c k (c k)
      rwa [Function.update_eq_self] at h
    have hP0 : P ≠ 0 := by
      intro h0
      apply hc
      rw [hcP, h0, mul_zero]
    have hmem : ∀ m : ι k, segreVec y (Function.update c k m) / segreVec y c ∈
        Subfield.closure (chartRing O (segreVec y) c : Set Ω) := fun m =>
      Subfield.subset_closure (Algebra.subset_adjoin ⟨Function.update c k m, rfl⟩)
    have key : y ⟨k, i⟩ / y ⟨k, j⟩ = (segreVec y (Function.update c k i) / segreVec y c) /
        (segreVec y (Function.update c k j) / segreVec y c) := by
      rw [div_div_div_cancel_right₀ hc, BirationalJoin.segreVec_update,
        BirationalJoin.segreVec_update, mul_div_mul_right _ _ hP0]
    show y ⟨k, i⟩ / y ⟨k, j⟩ ∈ _
    rw [key]
    exact Subfield.div_mem _ (hmem i) (hmem j)

theorem BirationalJoin.exists_div_of_mem_closure (S : Subalgebra O Ω) {x : Ω}
    (hx : x ∈ Subfield.closure (S : Set Ω)) : ∃ a ∈ S, ∃ b ∈ S, x = a / b := by
  have hS : Subring.closure (S : Set Ω) = S.toSubring := by
    rw [← Subalgebra.coe_toSubring]
    exact Subring.closure_eq _
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [hS] at ha hb
  exact ⟨a, ha, b, hb, rfl⟩

end Proof

theorem BirationalJoin.proof : BirationalJoin.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ y K₂ _ ι₂ _ w h c hc c₁ c₂ hc₂
  have hr : segreVec w c₁ / segreVec w c₂ ∈ fnField O y :=
    h ▸ BirationalJoin.segre_ratio_mem_fnField y w c₁ c₂
  obtain ⟨a, ha, b, hb, hab⟩ := BirationalJoin.exists_div_of_mem_closure _
    (BirationalJoin.fnField_le_closure_chartRing y c hc hr)
  by_cases hb0 : b = 0
  · have hw : segreVec w c₁ = 0 := by
      rw [hb0, div_zero, div_eq_zero_iff] at hab
      exact hab.resolve_right hc₂
    exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by rw [hw, zero_mul, zero_mul]⟩
  · exact ⟨a, ha, b, hb, hb0, (div_eq_div_iff hc₂ hb0).mp hab⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensSpan.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    exact ⟨n, by rw [← mul_assoc]; exact mul_mem hn (ht q)⟩

theorem TwistedDualGensSpan.proof : TwistedDualGensSpan.Statement := by
  unfold TwistedDualGensSpan.Statement
  intro R _ Ω _ _ K _ ι y N E _ _ B a M φ hφ c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  obtain ⟨β, hβ⟩ : ∃ β : Module.Basis (Fin N) Ω E, ∀ q, β q = b l0 q :=
    ⟨Module.Basis.mk (hli l0) (hsp l0).ge, fun q => Module.Basis.mk_apply _ _ _⟩
  have key : ∀ q, β.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have hden : ∀ l r, ∃ D ∈ chartRing R (segreVec y) c, D ≠ 0 ∧
        (f l ≠ 0 → D * β.coord q (b l r) ∈ chartRing R (segreVec y) c) := by
      intro l r
      by_cases hl : f l = 0
      · exact ⟨1, one_mem _, one_ne_zero, fun h => (h hl).elim⟩
      obtain ⟨n, hn⟩ := (hiff l (b l r)).2 ⟨Pi.single r 1, fun q' => ⟨0, by
        by_cases h : q' = r
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l0 _).1 ⟨0, by simpa using hn⟩
      obtain ⟨m, hm⟩ := ha' q
      refine ⟨f l0 ^ m * f l ^ n, mul_mem (pow_mem (hf l0) _) (pow_mem (hf l) _),
        mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl), fun _ => ?_⟩
      have hc' : β.coord q (f l ^ n • b l r) = a' q := by
        rw [hrep, show ∑ q, a' q • b l0 q = ∑ q, a' q • β q by simp [hβ],
          Module.Basis.coord_apply, Module.Basis.repr_sum_self]
      have : f l0 ^ m * f l ^ n * β.coord q (b l r) = f l0 ^ m * a' q := by
        rw [← hc', map_smul, smul_eq_mul]; ring
      rw [this]
      exact hm
    choose D hDA hD0 hDc using hden
    set d : Ω := ∏ p : Fin k × Fin N, D p.1 p.2 with hd
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 _ _
    have hdc : ∀ l r, f l ≠ 0 → d * β.coord q (b l r) ∈ chartRing R (segreVec y) c := by
      intro l r hl
      have hsplit := Finset.mul_prod_erase Finset.univ (fun p : Fin k × Fin N => D p.1 p.2)
        (Finset.mem_univ (l, r))
      dsimp only at hsplit
      rw [hd, ← hsplit]
      have : D l r * (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * β.coord q (b l r) =
          (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * (D l r * β.coord q (b l r)) := by ring
      rw [this]
      exact mul_mem (prod_mem fun p _ => hDA _ _) (hDc l r hl)
    have hψ : ∀ v ∈ B.lat c, (d • β.coord q) v ∈ chartRing R (segreVec y) c := by
      intro v hv
      rw [LinearMap.smul_apply, smul_eq_mul]
      refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
      intro l
      by_cases hl : f l = 0
      · exact ⟨1, by simp [hl]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
      obtain ⟨n, hn⟩ := TwistedDualGensSpan.sum_mul_mem_localized _ (hf l) a'
        (fun r => d * β.coord q (b l r)) ha' (fun r => hdc l r hl)
      refine ⟨n, ?_⟩
      have : d * β.coord q v = ∑ r, a' r * (d * β.coord q (b l r)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hrep, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, smul_eq_mul]; ring
      rw [smul_eq_mul, this]
      exact hn
    obtain ⟨u, -, hu⟩ := hφ.generate c hc (d • β.coord q) hψ
    have hmem : d • β.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have : β.coord q = d⁻¹ • (d • β.coord q) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  rw [eq_top_iff, ← β.dualBasis.span_eq, Module.Basis.coe_dualBasis]
  exact Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact key q)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleSectionForms.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N,
      ∃ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
        IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
        (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) ∧
        f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

