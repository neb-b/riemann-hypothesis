module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

namespace Relabel

section Eventual

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompOrderIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      have := h (e.symm k)
      simpa using this
    · intro h k
      exact h (e k)

theorem eventualValue_congr {K K' : Type*} {f : (K → ℤ) → ℤ} {g : (K' → ℤ) → ℤ}
    (h : ∀ c, (∀ᶠ m in atTop, f m = c) ↔ ∀ᶠ m in atTop, g m = c) :
    eventualValue f = eventualValue g := by
  unfold eventualValue
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · have hg : ∃ c, ∀ᶠ m in atTop, g m = c := hf.imp fun c hc => (h c).1 hc
    rw [dite_eq_left hf, dite_eq_left hg]
    have h1 := (h _).1 hf.choose_spec
    have h2 := hg.choose_spec
    obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
    exact hm1.symm.trans hm2
  · have hg : ¬ ∃ c, ∀ᶠ m in atTop, g m = c := fun ⟨c, hc⟩ => hf ⟨c, (h c).2 hc⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem eventualValue_precomp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  refine eventualValue_congr fun c => ?_
  rw [← (precompOrderIso e).map_atTop, Filter.eventually_map]
  rfl

theorem mixedDiff_precomp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

end Eventual

section Rename

variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]


include hφ in
theorem weight_mapDomain (d : (Σ k, ι₁ k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι₂) (Finsupp.mapDomain φ d) =
      Finsupp.weight (blockWeight ι₁) d ∘ e.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
    rfl
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hφ, Pi.smul_apply, Function.comp_apply, Pi.single_apply,
      Equiv.symm_apply_eq]


include hφ in
theorem gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    gradedPiece (I.map (renameEquiv F φ)) d =
      (gradedPiece I (d ∘ e)).map
        ((Ideal.quotientEquivAlg I (I.map (renameEquiv F φ)) (renameEquiv F φ) (Ideal.map_coe _ _).symm).toLinearEquiv :
          (MRing ι₁ F ⧸ I) →ₗ[F] MRing ι₂ F ⧸ I.map (renameEquiv F φ)) := by
  rw [gradedPiece_eq_span, gradedPiece_eq_span, Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearMap_apply, Ideal.quotientEquivAlg_mk, renameEquiv_apply, rename_monomial]
  constructor
  · rintro ⟨d₂, hd₂, rfl⟩
    refine ⟨Finsupp.mapDomain φ.symm d₂, ?_, ?_⟩
    · have h := weight_mapDomain e φ hφ (Finsupp.mapDomain φ.symm d₂)
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id, hd₂] at h
      funext k
      have := congrFun h (e k)
      simpa using this.symm
    · rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  · rintro ⟨d₁, hd₁, rfl⟩
    refine ⟨Finsupp.mapDomain φ d₁, ?_, rfl⟩
    rw [weight_mapDomain e φ hφ, hd₁]
    funext k
    simp


include hφ in
theorem finrank_gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    Module.finrank F (gradedPiece (I.map (renameEquiv F φ)) d) =
      Module.finrank F (gradedPiece I (d ∘ e)) := by
  rw [gradedPiece_map_rename e φ hφ, LinearEquiv.finrank_map_eq]


include hφ in
theorem hilbFn_map_rename (I : Ideal (MRing ι₁ F)) (m : K₂ → ℤ) :
    hilbFn (I.map (renameEquiv F φ)) m = hilbFn I (m ∘ e) := by
  unfold hilbFn
  have hpos : (∀ k, 0 ≤ m k) ↔ ∀ k, 0 ≤ (m ∘ e) k :=
    ⟨fun h k => h (e k), fun h k => by simpa using h (e.symm k)⟩
  by_cases h : ∀ k, 0 ≤ m k
  · rw [if_pos h, if_pos (hpos.1 h)]
    exact congrArg _ (finrank_gradedPiece_map_rename e φ hφ I (fun k => (m k).toNat))
  · rw [if_neg h, if_neg (mt hpos.2 h)]


include hφ in
theorem intNum_map_rename (I : Ideal (MRing ι₁ F)) {n : ℕ} (bs : Fin n → K₂ → ℤ) :
    intNum F (I.map (renameEquiv F φ)) bs = intNum F I (fun i => bs i ∘ e) := by
  unfold intNum
  have h : hilbFn (I.map (renameEquiv F φ)) = fun m => hilbFn I (m ∘ e) :=
    funext (hilbFn_map_rename e φ hφ I)
  rw [h, mixedDiff_precomp, eventualValue_precomp]

end Rename

end Relabel

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

namespace ContractRelDimLe

section Chain

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem ringKrullDim_killIdeal_add_card_le {Q : Ideal (MRing ι F)} [Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q)
    (T : Finset K) :
    ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  induction T using Finset.induction_on with
  | empty =>
    have : killIdeal Q (∅ : Finset K) = Q := by
      ext q
      simp [killIdeal, killBlocks_empty]
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
  | insert k T hk ih =>
    have : (killIdeal Q T).IsPrime := Ideal.comap_isPrime _ _
    have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
      (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
      (by
        change killBlocks T (X ⟨k, i k⟩) ∉ Q
        rw [killBlocks_X, if_neg hk]
        exact hi k)
      (by
        change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
        rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
        exact Q.zero_mem)
    calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
        = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
          rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
            add_comm (1 : WithBot ℕ∞)]
      _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
      _ ≤ _ := ih

end Chain

section Contract

variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)


omit [DecidableEq K] in
theorem killBlocks_compl_rename :
    (killBlocks (ι := ι') (F := F) (Finset.univ.map j)ᶜ).comp (rename (blockIncl j ι')) =
      rename (blockIncl j ι') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X, blockIncl]


omit [DecidableEq K] in
theorem exists_rename_eq_killBlocks_compl (x : MRing ι' F) :
    ∃ a : MRing (fun k => ι' (j k)) F,
      rename (blockIncl j ι') a = killBlocks (Finset.univ.map j)ᶜ x := by
  induction x using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [killBlocks]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
  | mul_X p v hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨k', i⟩ := v
    rw [map_mul, killBlocks_X, ← ha]
    by_cases h : k' ∈ (Finset.univ.map j)ᶜ
    · exact ⟨0, by rw [if_pos h, mul_zero, map_zero]⟩
    · rw [if_neg h]
      simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and, not_not] at h
      obtain ⟨k, rfl⟩ := h
      exact ⟨a * X ⟨k, i⟩, by rw [map_mul, rename_X]; rfl⟩

theorem ringKrullDim_contract_eq_killIdeal (P' : Ideal (MRing ι' F)) :
    ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') =
      ringKrullDim (MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ) := by
  set f : MRing (fun k => ι' (j k)) F →+* MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ :=
    (Ideal.Quotient.mk _).comp (rename (blockIncl j ι')).toRingHom
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_rename_eq_killBlocks_compl j ι' (F := F) x
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = _
    rw [Ideal.Quotient.eq, ha]
    change killBlocks _ (killBlocks _ x - x) ∈ P'
    rw [map_sub, ← AlgHom.comp_apply, killBlocks_comp le_rfl, sub_self]
    exact P'.zero_mem
  have hker : RingHom.ker f = contractPrime j P' := by
    ext a
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = 0 ↔ rename (blockIncl j ι') a ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change killBlocks _ (rename (blockIncl j ι') a) ∈ P' ↔ _
    rw [← AlgHom.comp_apply, killBlocks_compl_rename]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)

end Contract

theorem proof : ContractRelDimLe.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP'
  have := hP'.isPrime
  have hstab : ∀ (T : Finset K') (q : MRing ι' F), q ∈ P' → killBlocks T q ∈ P' :=
    fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq hstab hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (Q := contractPrime j P')
    (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
  have hchain := ringKrullDim_killIdeal_add_card_le hstab hP'.relevant (Finset.univ.map j)ᶜ
  rw [← ringKrullDim_contract_eq_killIdeal, hD, hD', ← Nat.cast_add] at hchain
  have hle : D + ((Finset.univ.map j)ᶜ).card ≤ D' := by exact_mod_cast hchain
  have hcard : ((Finset.univ.map j)ᶜ).card + Fintype.card K = Fintype.card K' := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ]
    have := Fintype.card_le_of_embedding j
    omega
  rw [relDim_eq_int hD, relDim_eq_int hD']
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))

end ContractRelDimLe

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem relDim_of_ringKrullDim_eq (I : Ideal (MRing ι F)) (d : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = (d : WithBot ℕ∞)) :
    relDim I = (((d : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  rfl


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem relDim_map_injective :
    Function.Injective (WithBot.map (fun d : ℕ∞ =>
      WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)) :=
  WithBot.map_injective (WithTop.map_injective fun a b h => by
    have h' : (a : ℤ) - Fintype.card K = (b : ℤ) - Fintype.card K := h
    omega)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial Filter

noncomputable section

theorem totalDegree_bind₁_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem EventuallyPolyShift.proof : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventuallyPolyUnique.proof : EventuallyPolyUnique.Statement := by
  intro K _ h p q hp hq
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hp.and hq)
  have hpq : p - q = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
      (fun k => (Finset.range ((p - q).degreeOf k + 1)).image
        (fun i : ℕ => ((M k + (i : ℤ) : ℤ) : ℚ)))
    · intro k
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        simpa using hab
    · intro x hx
      choose i _ hix using fun k => Finset.mem_image.1 (hx k)
      have hm : M ≤ fun k => M k + (i k : ℤ) := fun k => by simp
      have hxm : x = fun k => (((M k + (i k : ℤ) : ℤ)) : ℚ) := funext fun k => (hix k).symm
      obtain ⟨h1, h2⟩ := hM _ hm
      rw [map_sub, hxm, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 hpq

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem IntNumUnique.proof (h1 : CutRational.Statement.{u}) (h2 : IntNumBase.Statement.{u})
    (h3 : ExistsForm.Statement.{u}) (h4 : DivCycleSupport.Statement.{u}) :
    IntNumUnique.Statement.{u} := by
  intro F _ K _ _ ι _ N hN P hP n
  induction n generalizing P with
  | zero =>
    intro hdim bs
    have hbs : bs = ![] := Subsingleton.elim _ _
    subst hbs
    rw [hN.base P hP hdim]
    obtain ⟨-, h⟩ := h2 F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  | succ n ih =>
    intro hdim bs
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ := h3 F K ι P hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    rw [hbs, hN.cut P n hP hdim bf bg f g hf hg hfP hgP,
      h1 F K ι P hP n hdim bf bg f g hf hg hfP hgP]
    unfold cycEval
    congr 1
    funext W
    by_cases hW : ratDiv P f g W = 0
    · rw [hW, zero_mul, zero_mul]
    · have hsupp : IsMultiProjPrime W ∧ relDim W = (n : ℕ) := by
        unfold ratDiv at hW
        by_cases hfW : divCycle P f W = 0
        · have hgW : divCycle P g W ≠ 0 := by
            intro h
            apply hW
            rw [hfW, h, sub_zero]
          exact h4 F K ι P hP n hdim bg g hg hgP W hgW
        · exact h4 F K ι P hP n hdim bf f hf hfP W hfW
      simp only [ih W hsupp.1 hsupp.2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

