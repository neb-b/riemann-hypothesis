module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadic
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {d M : ℕ} (h : d ∣ M) {x y : ℤ} (hxy : (x : ZMod M) = y) : (x : ZMod d) = y :=
  (ZMod.intCast_eq_intCast_iff _ _ _).2
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff _ _ _).1 hxy))

theorem gamma_le {d M : ℕ} (h : d ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma d := by
  intro γ hγ
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_of_dvd h (x := γ 0 0) (y := 1) (by simpa using a)
  · simpa using cast_of_dvd h (x := γ 0 1) (y := 0) (by simpa using b)
  · simpa using cast_of_dvd h (x := γ 1 0) (y := 0) (by simpa using c)
  · simpa using cast_of_dvd h (x := γ 1 1) (y := 1) (by simpa using e)

theorem gamma_le_gam {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  obtain ⟨a, -, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hN hγ)
  obtain ⟨-, -, c', -⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hl hγ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨a, e, c⟩, CongruenceSubgroup.Gamma0_mem.2 c'⟩

theorem polySlash_eq_self_of_mem_Gamma (l n : ℕ) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n))
    (p : MvPolynomial (Fin 2) (ZMod (l ^ n))) : slP (δ : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  rw [GlobalTheory.KZ.SlPLaws.polySlash_congr _ 1 p, GlobalTheory.KZ.SlPLaws.polySlash_one']
  intro i j
  fin_cases i <;> fin_cases j <;> simp [a, b, c, e]

theorem toZModPow_eval (l : ℕ) [Fact l.Prime] (n : ℕ) (u : Fin 2 → ℤ_[l]) (p : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval u p) =
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (MvPolynomial.map (PadicInt.toZModPow n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem kum_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {ι : Type} (s : Finset ι) (x : ι → X.Khat l)
    (χ : ι → SL(2, ℤ) → ZMod (l ^ n)) (h : ∀ i ∈ s, Kum X l n (x i) (χ i)) :
    Kum X l n (∑ i ∈ s, x i) (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (_root_.GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (_root_.GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.KZ.H3.KumPot

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem bset_rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] [IsAlgClosed Ω] (hJ : JHol X) (N w : ℕ) (hN : 4 ≤ N)
    (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  obtain ⟨⟨c, hcA, hbc⟩, hinv⟩ := hb
  have hcoef := fun γ hγ i => _root_.GlobalTheory.KZ.H3.coef_of_inv Ω ε X l N w b c hbc γ hγ (hinv γ hγ) i
  obtain ⟨Φ, hΦ, hK⟩ := _root_.GlobalTheory.KZ.H3.kum_family Ω ε X l hJ N w c hcA hcoef
  obtain ⟨z, hz, hzΦ⟩ := _root_.GlobalTheory.KZ.H3.cocycle_lift_of_fam N l w (by omega) hl2 hlN hw Φ hΦ
  obtain ⟨F, hF, hFz⟩ := _root_.GlobalTheory.KZ.H3.exists_pot_of_isCoc ℤ_[l] w N l hN z hz
  refine ⟨F, hF, fun u n => ⟨fun δ => MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (Φ n δ), ?_, ?_⟩⟩
  · have hsum := kum_sum X l n (Finset.univ : Finset (Fin (w + 1))) (fun (i : Fin (w + 1)) => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i)
      (fun (i : Fin (w + 1)) δ => PadicInt.toZModPow n (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) *
        AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))))
      (fun i _ => GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ (hK n i))
    rw [← hbc u] at hsum
    convert hsum using 1
    funext δ
    rw [Finset.sum_apply]
    have MX := _root_.GlobalTheory.KZ.H3.mon_expand (ZMod (l ^ n)) w
    conv_lhs => rw [MX.2.1 (Φ n δ) (hΦ.1 n δ)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.eval_C, MX.2.2.2.1, map_pow]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · obtain ⟨M1, hM1, hM1'⟩ := hzΦ n
    have hl : 0 < l := (Fact.out : l.Prime).pos
    refine ⟨N * l ^ (n + 1) * M1, by positivity, fun δ hδ τ hτ => ?_⟩
    have hδG : δ ∈ Gam N l := gamma_le_gam (l := l) ⟨l ^ (n + 1) * M1, by ring⟩
      ⟨N * l ^ n * M1, by ring⟩ hδ
    have hδn : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := gamma_le ⟨N * l * M1, by ring⟩ hδ
    have hδ1 : δ ∈ CongruenceSubgroup.Gamma M1 := gamma_le ⟨N * l ^ (n + 1), by ring⟩ hδ
    have e1 := hFz δ hδG τ hτ
    have e2 : MvPolynomial.map (PadicInt.toZModPow n) (z δ) = Φ n δ := hM1' δ hδ1
    have e3 : MvPolynomial.map (PadicInt.toZModPow n) (F (mob (ofSL δ) τ)) =
        MvPolynomial.map (PadicInt.toZModPow n) (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) τ))) := by
      rw [GlobalTheory.KZ.SlPLaws.map_slP, polySlash_eq_self_of_mem_Gamma l n hδn]
    rw [map_sub, toZModPow_eval, toZModPow_eval, e3, ← map_sub, ← map_sub, e1, e2]

end GlobalTheory.KZ.H3.KumPot

theorem GlobalTheory.KZ.H3.exists_pot_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  intro Ω _ _ ε X l _ _ hJ N w hN hl2 hlN hw b hb
  have RO := _root_.GlobalTheory.KZ.H3.rel_ops Ω ε X l
  have PL := _root_.GlobalTheory.KZ.pot_triv_lin ℤ_[l] w (Gam N l)
  induction hb using Submodule.span_induction with
  | mem b hb => exact KumPot.bset_rel X l hJ N w hN hl2 hlN hw b hb
  | zero => exact ⟨0, PL.2.1, RO.2.1⟩
  | add b b' _ _ ih ih' =>
    obtain ⟨F, hF, hR⟩ := ih
    obtain ⟨F', hF', hR'⟩ := ih'
    exact ⟨F + F', PL.1 _ _ hF hF', RO.1 _ _ _ _ hR hR'⟩
  | smul a b _ ih =>
    obtain ⟨F, hF, hR⟩ := ih
    exact ⟨a • F, PL.2.2.1 a F hF, RO.2.2.1 a b F hR⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateField
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _


open GlobalTheory.FN.LevelGal in
theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroCommonZeroOfConstantCoeffEqZero
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_constantCoeff_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, MvPolynomial.constantCoeff (f i) = 0) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  classical
  set m : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) with hm
  have hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin n → k)) :=
    fun c => ⟨MvPolynomial.C c, by simp⟩
  haveI hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin n) k)) with hI
  have hIm : I ≤ m := by
    rw [hI, Ideal.span_le]
    intro g hg
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hg
    obtain ⟨i, rfl⟩ := hg
    simp [hm, RingHom.mem_ker, MvPolynomial.eval_zero, hf i]
  have hItop : I ≠ ⊤ := fun h => hmax.ne_top (top_le_iff.mp (h ▸ hIm))
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hItop
  haveI hPp : P.IsPrime := hP.1.1
  have hht : P.height ≤ r := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    refine h1.trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hmh : m.height = n := (ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n m).2
  have hPne : P ≠ m := by
    intro h
    rw [h, hmh] at hht
    exact absurd (by exact_mod_cast hht : n ≤ r) (not_le.mpr hrn)
  by_contra hcon
  push_neg at hcon
  apply hPne
  have hsub : MvPolynomial.zeroLocus k P ⊆ {0} := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (hP.1.2 (Ideal.subset_span (by simp)))
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  have hle : m ≤ P := by
    intro p hp
    have h2 : p ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) := by
      intro x hx
      rw [Set.mem_singleton_iff.mp (hsub hx)]
      exact hp
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hPp.radical] at h2
  exact (hmax.eq_of_le hPp.ne_top hle).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
section
open Polynomial

namespace GlobalTheory

theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.StabGal
theorem klm_sl_gal_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l M : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (d : ℤ) (γ γ'' : SL(2, ℤ)), 0 < M → IsPrimitiveRoot ζ M → s ζ = ζ ^ d → ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → ∀ y ∈ X.Lev l M, X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) = X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y) := by
  intro Ω _ _ ε X l M _ s ζ d γ γ'' hM hζ hsd hcong y hy
  refine Submodule.span_induction (p := fun y _ => X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) =
      X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨f, hf, rfl⟩
    have hr := X.recip M (f : X.K) hM hf ζ hζ s d hsd γ'' γ hcong
    simp only [Tower.klm, LinearMap.baseChange_tmul]
    congr 1
    apply Additive.toMul.injective
    apply Units.ext
    simp [hr]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro a x _ hx; simp [hx]

theorem galB_mem_Pol : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω), (∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.galB l s b ∈ X.Pol l w := by
  intro Ω _ _ ε X l w _ s hA b hb
  obtain ⟨c, hcA, hc⟩ := hb
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => Submodule.smul_mem _ _ (hA _ (hcA i)), fun u => ?_⟩
  show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
  rw [hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem eval_Pol_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ n : ℕ, ∃ y : Fin (w + 1) → X.Kl l, ∀ x : Fin 2 → ℤ_[l], ∃ Y ∈ Submodule.span ℤ_[l] (Set.range y), AdicCompletion.eval (idl l) (X.Kl l) n (b x) = Submodule.Quotient.mk Y := by
  intro Ω _ _ ε X l w _ b hb n
  obtain ⟨c, _, hc⟩ := hb
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  refine ⟨y, fun x => ⟨∑ i : Fin (w + 1), (x 0 ^ (i : ℕ) * x 1 ^ (w - (i : ℕ))) • y i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_sum]
  simp only [map_smul]
  change _ = Submodule.mkQ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, Submodule.mkQ_apply, hy]

theorem eval_Pol_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) → AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by
  intro Ω _ _ ε X l w _ b hb n u v huv
  obtain ⟨c, _, hc⟩ := hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  have hmem : (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ)) - v 0 ^ (i : ℕ) * v 1 ^ (w - (i : ℕ))) ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow,
      map_pow, map_pow, map_pow, huv 0, huv 1, sub_self]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hmem Submodule.mem_top

theorem twist_congr : ∀ (l n M : ℕ) [Fact l.Prime], l ^ n ∣ M → ∀ (γ γ'' : SL(2, ℤ)) (d : ℤ) (χ : ℤ_[l]), ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → (d : ZMod (l ^ n)) = PadicInt.toZModPow n χ → ∀ (u : Fin 2 → ℤ_[l]) (i : Fin 2), PadicInt.toZModPow n ((![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] : Fin 2 → ℤ_[l]) i) = PadicInt.toZModPow n ((mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i) := by
  intro l n M _ hlnM γ γ'' d χ hc hd u i
  obtain ⟨h00, h01, h10, h11⟩ := hc
  have cast : ∀ k : ℤ, ZMod.castHom hlnM (ZMod (l ^ n)) (k : ZMod M) = (k : ZMod (l ^ n)) := fun k => map_intCast _ k
  have e00 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h00
  have e01 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h01
  have e10 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h10
  have e11 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h11
  simp only [map_mul, cast] at e00 e01 e10 e11
  simp only [en] at e00 e01 e10 e11
  rw [hd] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dite_eq_left h]
  ext i j
  simp [ofSL]

theorem inv_galB {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s b := by
  obtain ⟨hpol, hinv⟩ := hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := eval_Pol_rep X l w b hpol n
  obtain ⟨M, hM, hdiv, hlev⟩ := _root_.GlobalTheory.KZ.Tower.exists_lev_family X l (N * l * l ^ n) y
    (Nat.mul_pos (Nat.mul_pos hN (Nat.Prime.pos Fact.out)) (pow_pos (Nat.Prime.pos Fact.out) n))
  have hNM : N ∣ M := Dvd.dvd.trans ⟨l * l ^ n, by ring⟩ hdiv
  have hlM : l ∣ M := Dvd.dvd.trans ⟨N * l ^ n, by ring⟩ hdiv
  have hlnM : l ^ n ∣ M := Dvd.dvd.trans ⟨N * l, by ring⟩ hdiv
  obtain ⟨γ'', hγ'', ζ, hζ, d, hsd, hcong, hdχ⟩ := _root_.GlobalTheory.exists_conj_level_exponent (Ω := Ω) N l n M hM hNM hlM hlnM s γ hγ
  have hspan : Submodule.span ℤ_[l] (Set.range y) ≤ X.Lev l M :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hlev i)
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := ![u 0, χ * u 1] with hv
  have h1 := eval_Pol_congr X l w b hpol n _ _ (twist_congr l n M hlnM γ γ'' d χ hcong hdχ u)
  obtain ⟨Y, hY, hYe⟩ := hy (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v)
  have hinv' : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) b v) =
      AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by rw [hinv γ'' hγ'']
  have hc := klm_sl_gal_comm X l M s ζ d γ γ'' hM hζ hsd hcong Y (hspan hY)
  show (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s) (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))).val n =
    (X.kmap l (X.gal s) (b v)).val n
  rw [toGQ_SL]
  change (X.klm l (X.sl (ofSL γ)).toRingEquiv).reduceModIdeal ((idl l)^n)
      ((X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b _))) =
    (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b v))
  rw [h1, hYe, ← hinv']
  change _ = (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n)
    ((X.klm l (X.sl (toGQ (γ'' : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv).reduceModIdeal ((idl l)^n)
      (AdicCompletion.eval (idl l) (X.Kl l) n (b (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v))))
  rw [toGQ_SL, hYe]
  simp only [LinearMap.reduceModIdeal_apply]
  rw [hc]

theorem galB_mem_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  intro Ω _ _ _ ε X hε hj N l w _ _ hN _ _ s b hb
  have hA := (_root_.GlobalTheory.KZ.kmap_A_stable ε X hε hj l).2 s
  have hN0 : 0 < N := by omega
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨galB_mem_Pol X l w s hA c hc.1, fun γ hγ => inv_galB X N l w hN0 s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

end GlobalTheory.KZ.StabGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansionStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
    IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
      ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.OrthDecomp.orth | exact GlobalTheory.K5.OrthDecomp.orth | (intros; apply GlobalTheory.K5.OrthDecomp.orth <;> assumption)
end

