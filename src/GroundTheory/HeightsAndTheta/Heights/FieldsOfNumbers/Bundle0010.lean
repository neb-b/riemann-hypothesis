module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

namespace MultEqualsCoeff

variable {K : Type*}

theorem tendsto_sub (c : K → ℤ) : Tendsto (fun m : K → ℤ => m - c) atTop atTop :=
  tendsto_atTop_atTop.2 fun a => ⟨a + c, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem foldr_diffStep_sum {J : Type*} (s : Finset J) (f : J → (K → ℤ) → ℤ) :
    ∀ L : List (K → ℤ), L.foldr diffStep (∑ j ∈ s, f j) = ∑ j ∈ s, L.foldr diffStep (f j)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_sum s f L]
      funext m
      simp only [diffStep, Finset.sum_apply, Finset.sum_sub_distrib]

theorem foldr_diffStep_zero : ∀ L : List (K → ℤ), L.foldr diffStep (0 : (K → ℤ) → ℤ) = 0
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons, foldr_diffStep_zero L]
      funext m
      simp [diffStep]

theorem foldr_diffStep_shift (h : (K → ℤ) → ℤ) (c : K → ℤ) :
    ∀ L : List (K → ℤ),
      L.foldr diffStep (fun m => h (m - c)) = fun m => L.foldr diffStep h (m - c)
  | [] => rfl
  | b :: L => by
      simp only [List.foldr_cons]
      rw [foldr_diffStep_shift h c L]
      funext m
      simp only [diffStep, sub_right_comm m b c]

theorem foldr_diffStep_eventuallyEq {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  | [] => e
  | b :: L => by
      have e' := foldr_diffStep_eventuallyEq e L
      filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2
      simp only [List.foldr_cons, diffStep]
      rw [h1, h2]

theorem exists_nat_of_nonneg_of_lt {x : WithBot (WithTop ℤ)} {n : ℕ} (h0 : 0 ≤ x)
    (h : x < n) : ∃ d : ℕ, x = d ∧ d < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h (not_lt.mpr (by simp))
    | coe z =>
      have hz0 : 0 ≤ z := by exact_mod_cast h0
      obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
      have hdn : (d : ℤ) < n := by exact_mod_cast h
      exact ⟨d, by norm_cast, by omega⟩

variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem relDim_nonneg_of_card_le (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by
  unfold relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe e =>
      have he : Fintype.card K ≤ e := by exact_mod_cast h
      have : (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) := by
        change (0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
        exact_mod_cast (by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)
      exact WithBot.coe_le_coe.mpr this

theorem hilbFn_eventually_zero_of_not_relevant (I : Ideal (MRing ι F)) (hI : ¬ IsRelevant I) :
    ∀ᶠ m in atTop, hilbFn I m = 0 := by
  simp only [IsRelevant, not_forall, not_exists, not_not] at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  unfold hilbFn
  split_ifs with h0
  · have hbot : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.as_sum f]
      refine Ideal.sum_mem _ fun s hs => ?_
      have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hs)
      obtain ⟨v, hv, hvk⟩ : ∃ v ∈ s.support, v.1 = k := by
        by_contra hne
        simp only [not_exists, not_and] at hne
        have h1 := congrFun hw k
        rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply,
          Finset.sum_eq_zero fun v hv => by
            simp [blockWeight, Ne.symm (hne v hv)]] at h1
        have := hm k
        simp only [Pi.one_apply] at this
        omega
      have hle : Finsupp.single v 1 ≤ s := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
      have hX : (X v : MRing ι F) ∈ I := by
        obtain ⟨k', i⟩ := v
        subst hvk
        exact hk i
      have e : monomial s (AddMonoidAlgebra.coeff f s) = X v * monomial (s - Finsupp.single v 1) (AddMonoidAlgebra.coeff f s) := by
        rw [show (X v : MRing ι F) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul,
          one_mul, add_tsub_cancel_of_le hle]
      rw [e]
      exact I.mul_mem_right _ hX
    rw [hbot]
    simp
  · rfl

end MultEqualsCoeff


open MultEqualsCoeff in
theorem MultEqualsCoeff.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : MixedDiffConst.Statement.{u}) (h3 : RelevantPrimeDimGe.Statement.{u}) :
    MultEqualsCoeff.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs
  classical
  obtain ⟨r, Q, c, hQ, hsum, hmult, hcase⟩ := h1 F K ι I hI
  let top : Ideal (MRing ι F) → Prop := fun W => W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n
  let val : Ideal (MRing ι F) → ℤ := fun W => if top W then intNum F W bs else 0
  have hpiece : ∀ j, ∀ᶠ m in atTop,
      mixedDiff bs (hilbFn (Q j)) (m - fun k => (c j k : ℤ)) = val (Q j) := by
    intro j
    refine (tendsto_sub fun k => (c j k : ℤ)).eventually
      (p := fun x => mixedDiff bs (hilbFn (Q j)) x = val (Q j)) ?_
    obtain ⟨hpr, hhom, -⟩ := hQ j
    by_cases hr : IsRelevant (Q j)
    · rcases (hcase j).resolve_left (not_not.mpr hr) with hlt | ⟨hmin, heq⟩
      · rw [hn] at hlt
        have hnt : ¬ top (Q j) := fun ht => lt_irrefl _ (ht.2.2 ▸ hlt)
        simp only [val, if_neg hnt]
        obtain ⟨d, hd, hdn⟩ := exists_nat_of_nonneg_of_lt
          (relDim_nonneg_of_card_le (Q j) (h3 F K ι (Q j) ⟨hpr, hhom, hr⟩)) hlt
        exact (h2 F K ι (Q j) hhom hr d hd).2 n hdn bs
      · have ht : top (Q j) := ⟨hmin, hr, heq.trans hn⟩
        simp only [val, if_pos ht]
        exact (h2 F K ι (Q j) hhom hr n (heq.trans hn)).1 bs
    · have hnt : ¬ top (Q j) := fun ht => hr ht.2.1
      simp only [val, if_neg hnt]
      filter_upwards [foldr_diffStep_eventuallyEq
        (hilbFn_eventually_zero_of_not_relevant (Q j) hr) (List.ofFn bs)] with m hm
      unfold mixedDiff
      rw [hm]
      exact congrFun (foldr_diffStep_zero _) m
  have hI' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = ∑ j, val (Q j) := by
    have e1 : mixedDiff bs (hilbFn I) =ᶠ[atTop]
        mixedDiff bs (∑ j, fun m => hilbFn (Q j) (m - fun k => (c j k : ℤ))) := by
      apply foldr_diffStep_eventuallyEq
      filter_upwards [hsum] with m hm
      rw [hm, Finset.sum_apply]
    filter_upwards [e1, eventually_all.2 hpiece] with m hm hall
    rw [hm, mixedDiff, foldr_diffStep_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [foldr_diffStep_shift]
    exact hall j
  have hval : intNum F I bs = ∑ j, val (Q j) := by
    obtain ⟨m, ha, hb⟩ := (((h2 F K ι I hI hrel n hn).1 bs).and hI').exists
    rw [← ha, hb]
  have hsupp : (Function.support fun W => topCycle I n W * intNum F W bs) ⊆
      (Finset.univ.image Q : Set (Ideal (MRing ι F))) := by
    intro W hW
    by_contra hWQ
    apply hW
    simp only [topCycle]
    split_ifs with h
    · have hm := hmult W h.1 h.2.1 (h.2.2.trans hn.symm)
      have h0 : (Finset.univ.filter fun j => Q j = W) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro rfl
        exact hWQ (by simp)
      rw [h0, Finset.card_empty] at hm
      rw [← hm]
      simp
    · simp
  rw [hval, cycEval, finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Q) (g := Q)
      (fun j _ => Finset.mem_image_of_mem Q (Finset.mem_univ j)) (fun j => val (Q j))]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  simp only [topCycle, val, top]
  split_ifs with h
  · rw [← hmult W h.1 h.2.1 (h.2.2.trans hn.symm)]
    simp
  · simp

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Pull

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem extend_apply_self {M : Type*} [Zero M] (b : K → M) (k : K) :
    Function.extend j b 0 (j k) = b k :=
  j.injective.extend_apply b 0 k

theorem extend_apply_not {M : Type*} [Zero M] (b : K → M) (k' : K') (h : ¬ ∃ k, j k = k') :
    Function.extend j b 0 k' = 0 := by
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem extend_inj {M : Type*} [Zero M] {b₁ b₂ : K → M} :
    Function.extend j b₁ 0 = Function.extend j b₂ 0 ↔ b₁ = b₂ := by
  refine ⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩
  have := congrFun h (j k)
  rwa [extend_apply_self, extend_apply_self] at this

theorem weight_apply_eval {σ : Type*} (w : σ → K' → ℕ) (d : σ →₀ ℕ) (k' : K') :
    Finsupp.weight w d k' = Finsupp.weight (fun v => w v k') d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

variable [DecidableEq K] [DecidableEq K']


omit [DecidableEq K] [DecidableEq K'] in
theorem weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (g : σ → τ)
    (d : σ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain g d) = Finsupp.weight (w ∘ g) d := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem weight_blockIncl (d : (Σ k, ι' (j k)) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain (blockIncl j ι') d) =
      Function.extend j (Finsupp.weight (blockWeight (fun k => ι' (j k))) d) 0 := by
  rw [weight_mapDomain]
  funext k'
  rw [weight_apply_eval]
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [extend_apply_self, weight_apply_eval]
    have e : (fun v => (blockWeight ι' ∘ blockIncl j ι') v (j k)) =
        fun v => blockWeight (fun k => ι' (j k)) v k := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) (j k) = (Pi.single v.1 1 : K → ℕ) k
      simp only [Pi.single_apply, j.injective.eq_iff]
    rw [e]
  · rw [extend_apply_not j _ k' h]
    have h0 : (fun v => (blockWeight ι' ∘ blockIncl j ι') v k') = 0 := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) k' = 0
      rw [Pi.single_apply, if_neg (fun hv => h ⟨v.1, hv.symm⟩)]
    rw [h0]
    simp [Finsupp.weight_apply]

variable {F : Type u} [Field F]

theorem isMultiHomog_rename {a : MRing (fun k => ι' (j k)) F} {c : K → ℕ} (ha : IsMultiHomog a c) :
    IsMultiHomog (rename (blockIncl j ι') a) (Function.extend j c 0) := by
  classical
  have ha' : IsWeightedHomogeneous (blockWeight (fun k => ι' (j k))) a c := ha
  show IsWeightedHomogeneous _ _ _
  intro d' hd'
  have hmem : d' ∈ (rename (blockIncl j ι') a).support := mem_support_iff.mpr hd'
  rw [support_rename_of_injective (blockIncl_injective j ι')] at hmem
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmem
  rw [weight_blockIncl, ha' (mem_support_iff.mp hd)]

theorem rename_component (a : MRing (fun k => ι' (j k)) F) (b : K → ℕ) :
    rename (blockIncl j ι') (weightedHomogeneousComponent (blockWeight (fun k => ι' (j k))) b a) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0)
        (rename (blockIncl j ι') a) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain (blockIncl j ι') d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain _ (blockIncl_injective j ι'),
      coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_weightedHomogeneousComponent,
      weight_blockIncl]
    by_cases hw : Finsupp.weight (blockWeight (fun k => ι' (j k))) d = b
    · rw [if_pos hw, if_pos (by rw [hw])]
    · rw [if_neg hw, if_neg (fun h => hw ((extend_inj j).mp h))]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ d' (fun u hu => absurd hu (hd u)),
      coeff_rename_eq_zero _ a d' (fun u hu => absurd hu (hd u))]
    simp

theorem isMultiProjPrime_contractPrime {P' : Ideal (MRing ι' F)} (hP' : IsMultiProjPrime P') :
    IsMultiProjPrime (contractPrime j P') := by
  have := hP'.isPrime
  refine ⟨contractPrime.isPrime j P', ?_, ?_⟩
  · intro f hf b
    show rename (blockIncl j ι') _ ∈ P'
    rw [rename_component]
    exact hP'.multiHomog _ hf _
  · intro k
    obtain ⟨i, hi⟩ := hP'.relevant (j k)
    refine ⟨i, ?_⟩
    show rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
    rw [rename_X]
    exact hi


omit [DecidableEq K] [DecidableEq K'] in
theorem contractFracMap_algebraMap (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (a : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') a)) =
      algebraMap _ (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') a)) := by
  unfold contractFracMap
  exact IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P')).toRingHom)
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective) _

theorem map_homFracDegZero_le (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_⟩
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]


omit [DecidableEq K] [DecidableEq K'] in
theorem pullDeg_sub (bf bg : K → ℕ) :
    pullDeg j (fun k => (bf k : ℤ) - bg k) =
      fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ) := by
  funext k'
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    simp only [pullDeg, extend_apply_self]
  · simp only [pullDeg, extend_apply_not j _ k' h]
    simp

end Pull

theorem ProjectionFormulaDegree.proof (h1 : CutRational.Statement.{u})
    (h2 : IntNumBase.Statement.{u}) (h3 : ProjectionFormulaContracted.Statement.{u})
    (h4 : DivPushForward.Statement.{u}) : ProjectionFormulaDegree.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n
  induction n generalizing P' with
  | zero =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    have e1 : (fun i : Fin 0 => pullDeg j (bs i)) = ![] := Subsingleton.elim _ _
    have e2 : bs = ![] := Subsingleton.elim _ _
    rw [e1, e2, (h2 F K' ι' P' hP' hdim).2, (h2 F K _ _ hP hdimP).2,
      ← IntermediateField.finrank_bot_mul_relfinrank (map_homFracDegZero_le j ι' P'),
      ← (IntermediateField.equivMap _ (contractFracMap j P')).toLinearEquiv.finrank_eq]
    unfold relDeg
    push_cast
    ring
  | succ n ih =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ :=
      ExistsForm.proof F K (fun k => ι' (j k)) (contractPrime j P') hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    have hpull : (fun i => pullDeg j (bs i)) = Fin.snoc (α := fun _ => K' → ℤ)
        (fun i => pullDeg j (Fin.init bs i))
        (fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ)) := by
      rw [← pullDeg_sub, hb]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, Fin.init]
    have hcutP : intNum F (contractPrime j P') bs =
        cycEval (fun W => intNum F W (Fin.init bs)) (ratDiv (contractPrime j P') f g) := by
      conv_lhs => rw [hbs]
      exact h1 F K _ _ hP n hdimP bf bg f g hf hg hfP hgP (Fin.init bs)
    have hcutP' := h1 F K' ι' P' hP' n hdim _ _ (rename (blockIncl j ι') f)
      (rename (blockIncl j ι') g) (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg)
      hfP hgP (fun i => pullDeg j (Fin.init bs i))
    have hyp1 : ∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) =
          relDeg j W' * intNum F (contractPrime j W') (Fin.init bs) :=
      fun W' hW' hd hc => (ih W' hW' hd hc (Fin.init bs)).2
    have hyp2 : ∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) →
        relDim (contractPrime j W') < (n : ℕ) →
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) = 0 :=
      fun W' hW' hd hlt => h3 F K K' j ι' W' hW' n hd hlt (Fin.init bs)
    have hpf := h4 F K K' j ι' P' hP' n hdim hdimP bf f hf hfP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    have hpg := h4 F K K' j ι' P' hP' n hdim hdimP bg g hg hgP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    rw [hpull, hcutP', hcutP, cycEval_ratDiv, cycEval_ratDiv, mul_sub, hpf, hpg]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

