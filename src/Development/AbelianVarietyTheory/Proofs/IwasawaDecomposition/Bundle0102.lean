module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

theorem isTorsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] isTorsionFree_field

section Avatar

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

def toQ (κ : FractionRing O →+* Qbar l) : O →+* Qbar l := κ.comp (algebraMap O (FractionRing O))

def inQ (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) : G E Ω →* (Qbar l)ˣ :=
  (Units.map (toQ κ).toMonoidHom).comp r

def IsGal [TopologicalSpace O] (art : Ideles E →* Gab E Ω) (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
    (χ : HChar E) (n : (E →+* ℂ) → ℤ) (r : G E Ω →* Oˣ) : Prop :=
  IsAlgPos χ n ∧ Continuous (fun g => ((r g : Oˣ) : O)) ∧ IsLAdicOf art ι χ n (inQ κ r)

def sideIso (ι : Qbar l ≃+* ℂ) (b : Bool) : Qbar l ≃+* ℂ :=
  if b then ι else ι.trans (starRingAut : ℂ ≃+* ℂ)

def block (μ η : HChar E) (r : ℕ) : HChar E := μ * (η⁻¹ * Model.absPow E (-(r : ℝ) / 2))

end Avatar

section Universal

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω]

def delAt {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (l : ℕ) : HChar H.E :=
  if l = H.pde then C.del' else C.del

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

def pair (P : PlE H) : Set (PlE H) := {v | v = P ∨ IsConjPl H P v}

variable {H}

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' :=
  (GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv P).unique
    ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P').1 h) ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P'').1 h')

theorem pair_eq {P P' : PlE H} (h : IsConjPl H P P') : pair H P' = pair H P := by
  ext v
  constructor
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique hv (isConjPl_symm h))
  · rintro (rfl | hv)
    · exact Or.inr (isConjPl_symm h)
    · exact Or.inl (isConjPl_unique hv h)

variable (H) (cc : Ω ≃+* Ω) (l : ℕ)

def IsDel (M : ℕ) (T : Set (PlE H)) (d : G H.E Ω →* Multiplicative (ZMod (l ^ M))) : Prop :=
  IsOpen (d.ker : Set (G H.E Ω)) ∧ AntiHom cc d ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ ReciprocityTheory.Gal.Dec (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∈ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := H.E) A, d σ = c)


open Classical in
def delOf (M : ℕ) (T : Set (PlE H)) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if h : ∃ d, IsDel H cc l M T d then h.choose else 1

theorem isDel_delOf {M : ℕ} {T : Set (PlE H)} (h : ∃ d, IsDel H cc l M T d) : IsDel H cc l M T (delOf H cc l M T) := by
  rw [delOf, dite_eq_left h]
  exact h.choose_spec

theorem delOf_laws (M : ℕ) (T : Set (PlE H)) :
    IsOpen ((delOf H cc l M T).ker : Set (G H.E Ω)) ∧ AntiHom cc (delOf H cc l M T) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ ReciprocityTheory.Gal.Dec (F := H.E) A,
      delOf H cc l M T σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delOf H cc l M T σ = 1) := by
  by_cases h : ∃ d, IsDel H cc l M T d
  · obtain ⟨h1, h2, h3, h4, -⟩ := isDel_delOf H cc l h
    exact ⟨h1, h2, h3, h4⟩
  · rw [delOf, dite_eq_right h]
    refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩


open Classical in
def delCoord (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if pair H P ⊆ ↑Q then delOf H cc l M (pair H P) else 1

def delU (Q : Finset (PlE H)) (M : ℕ) : G H.E Ω →* Multiplicative (DelQM H l Q M) where
  toFun σ := Multiplicative.ofAdd fun P => Multiplicative.toAdd (delCoord H cc l Q M P.1 σ)
  map_one' := by simp only [map_one, toAdd_one]; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

theorem delU_apply (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) (P : ↥Q) :
    Multiplicative.toAdd (delU H cc l Q M σ) P = Multiplicative.toAdd (delCoord H cc l Q M P.1 σ) := rfl

theorem delU_eq_one_iff (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) :
    delU H cc l Q M σ = 1 ↔ ∀ P ∈ Q, delCoord H cc l Q M P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem delCoord_laws (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) :
    IsOpen ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) ∧ AntiHom cc (delCoord H cc l Q M P) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ ReciprocityTheory.Gal.Dec (F := H.E) A,
      delCoord H cc l Q M P σ = 1) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      delCoord H cc l Q M P σ = 1) := by
  unfold delCoord
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := delOf_laws H cc l M (pair H P)
    exact ⟨h1, h2, h3, fun v hv => h4 v fun hm => hv (h hm)⟩
  · refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem delCoord_of_closed {Q : Finset (PlE H)} (hQ : ∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) (M : ℕ) {P : PlE H}
    (hP : P ∈ Q) : delCoord H cc l Q M P = delOf H cc l M (pair H P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

def UniversalAnticyclotomicCharLaws : Prop :=
  (∀ Q M v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ ReciprocityTheory.Gal.Dec (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M, AntiHom cc (delU H cc l Q M)) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU H cc l Q M).ker : Set (G H.E Ω))) ∧
  (∀ (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E Ω) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU H cc l Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, h hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E Ω,
      Multiplicative.toAdd (delU H cc l Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (l ^ M)) * Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) → ∀ (P : PlE H) (hP : P ∈ Q) (σ : G H.E Ω),
    Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delOf H cc l M (pair H P) σ)) ∧
  ∀ (M : ℕ) (P : PlE H), (∃ d, IsDel H cc l M (pair H P) d) → IsDel H cc l M (pair H P) (delOf H cc l M (pair H P))

theorem universal_anticyclotomic_character_laws : UniversalAnticyclotomicCharLaws H cc l := by
  refine ⟨fun Q M v hv A hA σ hσ => ?_, fun Q M v hv A hA σ hσ => ?_, fun Q M g g' h => ?_, fun Q M => ?_,
    fun M Q' Q h h1 h2 σ P hP => ?_, fun Q M P hP P' hP' h => ⟨1, fun σ => ?_⟩, fun Q M hQ P hP σ => ?_,
    fun M P h => isDel_delOf H cc l h⟩
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.2 v hv A hA σ hσ
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.1 v hv A hA σ hσ
  · exact Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((delCoord_laws H cc l Q M P.1).2.1 g g' h))
  · have e : ((delU H cc l Q M).ker : Set (G H.E Ω)) = ⋂ P ∈ Q, ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, delU_eq_one_iff]
    rw [e]
    exact isOpen_biInter_finset fun P _ => (delCoord_laws H cc l Q M P).1
  · rw [delU_apply, delU_apply, delCoord_of_closed H cc l h1 M hP, delCoord_of_closed H cc l h2 M (h hP)]
  · rw [delU_apply, delU_apply]
    have e : delCoord H cc l Q M P' = delCoord H cc l Q M P := by
      unfold delCoord
      rw [pair_eq h]
    simp only [e, Units.val_one, Int.cast_one, one_mul]
  · rw [delU_apply, delCoord_of_closed H cc l hQ M hP]

end Universal

theorem delUTie_of_exists {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (hY : ∀ i Q M, Y.delU i Q M = delU D.host X.cc (X.l i) Q M)
    (h : GlobalTheory.TwSys.K1 X) : GlobalTheory.TwSys.DelUTie Y := by
  intro i M _ hM
  obtain ⟨H', S, d, h1, h2, h3, h4⟩ := h i M hM
  refine ⟨H', S, fun P => delOf D.host X.cc (X.l i) M (pair D.host P), ⟨h1, h2, h3, fun P a b c => ?_⟩,
    fun Q hQ P hP σ => ?_⟩
  · exact isDel_delOf D.host X.cc (X.l i) ⟨d P, h4 P a b c⟩
  · rw [hY]
    exact (universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.2.1 Q M hQ P hP σ

end GlobalTheory.GalChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne
section
open NumberField IsDedekindDomain Formalism.L2.Host IsLocalRing Polynomial

namespace GlobalTheory.Mem.WildChar

theorem le_exp_neg_one_of_lt_one {g : WithZero (Multiplicative ℤ)} (hy : g < 1) :
    g ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_pow_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation K Γ) {a b : K} (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) :
    w (a ^ m - b ^ m) ≤ w (a - b) := by
  first
  | exact @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
  | (apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le ..)

theorem val_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) :
    w (u ^ q - 1) ≤ w (u - 1) * WithZero.exp (-1 : ℤ) := by
  rw [← mul_geom_sum, map_mul]
  refine mul_le_mul_right (le_exp_neg_one_of_lt_one ?_) _
  have e : ∑ i ∈ Finset.range q, u ^ i = (q : K) + ∑ i ∈ Finset.range q, (u ^ i - 1 ^ i) := by
    simp
  rw [e]
  refine Valuation.map_add_lt _ hq (Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_)
  exact (val_pow_sub_pow_le w hu (map_one w).le i).trans_lt hu1

theorem val_pow_pow_sub_one_le {K : Type*} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))
    {u : K} (hu : w u ≤ 1) (hu1 : w (u - 1) < 1) {q : ℕ} (hq : w (q : K) < 1) (n : ℕ) :
    w (u ^ (q ^ n) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero => simpa using hu1.le
  | succ n ih =>
    have h1 : w (u ^ (q ^ n)) ≤ 1 := by rw [map_pow]; exact pow_le_one' hu _
    have h2 : w (u ^ (q ^ n) - 1) < 1 := by
      have := val_pow_sub_pow_le w hu (map_one w).le (q ^ n)
      rw [one_pow] at this
      exact this.trans_lt hu1
    rw [pow_succ, pow_mul]
    refine (val_pow_sub_one_le w h1 h2 hq).trans ((mul_le_mul_left ih _).trans (le_of_eq ?_))
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem valued_algebraMap_lt_one {y : 𝓞 L} :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) < 1 ↔ y ∈ v.asIdeal := by
  have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y)
      = v.valuation L (algebraMap (𝓞 L) L y) :=
    ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L y)
  rw [h3]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem valued_absNorm_lt_one :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion L) < 1 := by
  rw [← map_natCast (algebraMap (𝓞 L) (v.adicCompletion L)), valued_algebraMap_lt_one]
  exact Ideal.absNorm_mem v.asIdeal

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem valued_pow_sub_one_lt_one {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    Valued.v (x ^ (Ideal.absNorm v.asIdeal - 1) - 1) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v x hx.le
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx]
    exact hy
  have hnot : y ∉ v.asIdeal := by
    rw [← valued_algebraMap_lt_one, hy1]; exact lt_irrefl _
  have hmem : y ^ (Ideal.absNorm v.asIdeal - 1) - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
    rw [← Ideal.Quotient.eq, map_pow, map_one, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (fun h => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h))
  rw [← valued_algebraMap_lt_one, map_sub, map_pow, map_one] at hmem
  rw [← sub_add_sub_cancel _
    (algebraMap (𝓞 L) (v.adicCompletion L) y ^ (Ideal.absNorm v.asIdeal - 1))]
  exact Valuation.map_add_lt _ ((val_pow_sub_pow_le _ hx.le hy1.le _).trans_lt hy) hmem

theorem mem_maximalIdeal_iff (a : v.adicCompletionIntegers L) :
    a ∈ maximalIdeal (v.adicCompletionIntegers L) ↔ Valued.v (a : v.adicCompletion L) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h : Valued.v (a : v.adicCompletion L) ≤ 1 := a.2
  exact ⟨fun h' => lt_of_le_of_ne h h', fun h' => h'.ne⟩

theorem exists_rootOfUnity_congr {x : v.adicCompletion L} (hx : Valued.v x = 1) :
    ∃ ζ : v.adicCompletion L, ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 ∧ Valued.v (ζ - x) < 1 := by
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers L))
      (v.adicCompletionIntegers L) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  have hq := one_lt_absNorm v
  let a : v.adicCompletionIntegers L := ⟨x, hx.le⟩
  obtain ⟨ζ, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers L))
    (X ^ (Ideal.absNorm v.asIdeal - 1) - C 1) (monic_X_pow_sub_C _ (by omega)) a
    (by
      rw [mem_maximalIdeal_iff]
      simpa [a] using valued_pow_sub_one_lt_one v hx)
    (by
      apply IsUnit.map
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have h3 : Valued.v (((Ideal.absNorm v.asIdeal - 1 : ℕ)) : v.adicCompletion L) = 1 := by
        rw [Nat.cast_sub hq.le, Nat.cast_one, Valuation.map_sub_swap]
        exact Valuation.map_one_sub_of_lt _ (valued_absNorm_lt_one v)
      simp [a, derivative_X_pow, hx, h3])
  refine ⟨ζ, ?_, ?_⟩
  · have h4 : ζ ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      simpa [sub_eq_zero] using h1
    have h5 := congrArg (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) h4
    rw [map_pow, map_one] at h5
    exact h5
  · have h6 := (mem_maximalIdeal_iff v _).1 h2
    rw [AddSubgroupClass.coe_sub] at h6
    exact h6

theorem orders_on_units : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)), (χ.TameAt v → ∀ x, IsUnitAt v x → χ.loc v x ^ (Ideal.absNorm v.asIdeal - 1) = 1) ∧ ((∀ x : (v.adicCompletion L)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1) → ∀ x, IsUnitAt v x → ∃ n : ℕ, χ.loc v x ^ (Ideal.absNorm v.asIdeal ^ n) = 1) := by
  intro L _ _ χ v
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [← map_pow]
    refine h _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
    rw [Units.val_pow_eq_pow_val]
    simpa using le_exp_neg_one_of_lt_one (valued_pow_sub_one_lt_one v hx)
  · obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
    have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
    obtain ⟨ζ, h1, h2⟩ := exists_rootOfUnity_congr v hx'
    have hζ : Valued.v ζ = 1 := by
      rw [← hx']
      apply Valuation.map_eq_of_sub_lt
      rwa [hx']
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ
    let z : (v.adicCompletion L)ˣ := Units.mk0 ζ h0
    have hz : χ.loc v z = 1 := h z (Units.ext (by simpa [z] using h1))
    have hu : IsUnitAt v (x * z⁻¹) := by
      simp [IsUnitAt, z, hx', hζ]
    have hu1 : Valued.v (((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) < 1 := by
      have e : ((x * z⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = (x - ζ) * ζ⁻¹ := by
        simp [z, sub_mul, h0]
      rw [e, map_mul, map_inv₀, hζ, inv_one, mul_one, Valuation.map_sub_swap]
      exact h2
    refine ⟨n, ?_⟩
    have h3 := hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu (Ideal.absNorm v.asIdeal ^ n)) (by
      rw [Units.val_pow_eq_pow_val]
      exact val_pow_pow_sub_one_le _ (le_of_eq hu) hu1 (valued_absNorm_lt_one v) n)
    rwa [map_pow, map_mul, map_inv, hz, inv_one, mul_one] at h3

end GlobalTheory.Mem.WildChar
end

