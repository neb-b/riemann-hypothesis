module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeyl
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem initMinor_mem_dualWeyl_ind (R : Type) [CommRing R] {r n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin r) :
    initMinor R I hs ∈ dualWeyl R r n (fun t => if t.val < s then 1 else 0) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [e1, e2] at h

private lemma one_mem_dualWeyl_zero (R : Type) [CommRing R] (r n : ℕ) :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]
  exact ⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩

private lemma mul_mem_dualWeyl_add (R : Type) [CommRing R] {r n : ℕ} {ν₁ ν₂ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν₁) (hg : g ∈ dualWeyl R r n ν₂) :
    f * g ∈ dualWeyl R r n (ν₁ + ν₂) := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem prod_mem_dualWeyl_sum (R : Type) [CommRing R] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) R) (hg : ∀ k, g k ∈ dualWeyl R r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl R r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_zero R r n
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_add R (hg a) ih

theorem exists_cofAct_initMinor (R : Type) [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin n) :
    ∃ g ∈ dualWeyl R n n (fun t => if 0 < s ∧ t.val < n - s then 1 else 0),
      (genM R n).det ^ (s - 1) * g = cofAct R n (initMinor R I hs) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine ⟨1, ?_, ?_⟩
    · convert one_mem_dualWeyl_zero R n n using 2
      funext t
      simp
    · simp [initMinor]
  by_cases hI : Function.Injective I
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by
      let e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)
      refine ⟨e.extendSubtype, fun a => ?_⟩
      rw [Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]
      simp only [e, Equiv.trans_apply]
      rw [Equiv.ofInjective_symm_apply]
      rfl
    obtain ⟨ε, hε⟩ := cofAct_initMinor R n s hs h1 σ
    have hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I := funext hσ
    rw [hIσ] at hε
    refine ⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      (Nat.sub_le n s), ?_, ?_⟩
    · have hm := initMinor_mem_dualWeyl_ind R (Nat.sub_le n s)
        (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      have hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) =
          fun t : Fin n => if t.val < n - s then 1 else 0 := by
        funext t
        simp [h1]
      rw [hw]
      exact zsmul_mem hm _
    · rw [hε, mul_smul_comm]
  · refine ⟨0, zero_mem _, ?_⟩
    simp only [Function.Injective, not_forall, exists_prop] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      exact Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])
    rw [h0, map_zero, mul_zero]

theorem nuDual_shapeDeg {m K : ℕ} (sz : Fin K → ℕ) :
    nuDual (shapeDeg sz : Fin (m + 1) → ℕ) =
      ∑ k, fun t : Fin (m + 1) => if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0 := by
  funext t
  have key : ∀ k, ((if t.rev.val < sz k then 1 else 0) +
      (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) =
        if (0 : Fin (m + 1)).val < sz k then 1 else 0 := by
    intro k
    have := t.isLt
    rw [Fin.val_rev]
    split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  have hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) +
      ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) =
        ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  simp only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]
  omega

private lemma card_filter_fin_val_lt_eq_of_le {N a : ℕ} (h : a ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < a).card = a := by
  have e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem sum_shapeDeg_sub {m K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ m + 1) :
    ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i - (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (sz k - 1) := by
  have h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k := by
    simp only [shapeDeg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_filter]
    exact card_filter_fin_val_lt_eq_of_le (hsz k)
  have h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    simp only [shapeDeg, Finset.card_filter]
  have h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  rw [h1, h0]
  omega

theorem exists_cofRel_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν _ _ f hf
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R (m + 1) (m + 1) ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨K, sz, hsz, I, hsh, -, hbi⟩ := (hb i).2.2
    rw [hbi]
    choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)
    refine ⟨∏ k, g k, ?_, ?_⟩
    · have hm := prod_mem_dualWeyl_sum R Finset.univ _ g hg
      rwa [← nuDual_shapeDeg sz, hsh] at hm
    · show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)
      rw [← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant,
        map_prod]
      exact Finset.prod_congr rfl fun k _ => hgeq k
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    refine ⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩
    unfold CofRel at e₁ e₂ ⊢
    rw [mul_add, e₁, e₂, map_add (f := _)]
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    refine ⟨a • g, Submodule.smul_mem _ a h, ?_⟩
    unfold CofRel at e ⊢
    rw [mul_smul_comm, e, map_smul]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.IdeleClass

variable (E : Type) [Field E] [NumberField E]

theorem localIdele_snd_self' (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

theorem localIdele_snd_ne' (v w : HeightOneSpectrum (𝓞 E)) (h : w ≠ v) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

theorem classHom_val (a : Ideles E) :
    ((((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) := rfl

theorem finIdele_apply (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.Mem.UnitIndex.finIdele E a : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v =
      (a : AdeleRing (𝓞 E) E).2 v := rfl

theorem classHom_eq_one_of_mem_unitIdl {a : Ideles E} (ha : a ∈ GlobalTheory.Mem.Chr.unitIdl E) :
    GlobalTheory.Mem.UnitIndex.classHom E a = 1 := by
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq]
    exact (GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1 :=
    Units.ext (by rw [classHom_val, h]; rfl)
  show ClassGroup.mk E _ = 1
  rw [hu, map_one]

theorem unitIdl_le_ker : GlobalTheory.Mem.Chr.unitIdl E ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker :=
  fun _ ha => classHom_eq_one_of_mem_unitIdl E ha

theorem infConn_le_unitIdl : infConn E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  rintro _ ⟨y, -, rfl⟩ v
  show Valued.v (1 : v.adicCompletion E) = 1
  exact map_one _

theorem diagUnits_range_le_ker : (diagUnits E).range ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker := by
  rintro _ ⟨k, rfl⟩
  have hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) =
      FiniteAdeleRing.unitEmbedding (𝓞 E) E k := Units.ext rfl
  show ClassGroup.mk E _ = 1
  rw [ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(k : E), rfl⟩⟩

theorem localIdele_mem_unitIdl (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self']
    exact hx
  · rw [localIdele_snd_ne' E v w hw]
    exact map_one _

open Classical in
theorem ord_vw_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) w =
      if v = w then 1 else 0 := by
  rw [GlobalTheory.Idele.ord_vw, finIdele_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self', if_pos rfl]
    have hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1) := hx
    rw [hx', WithZero.log_exp]
    rfl
  · rw [localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]
    rfl

theorem classHom_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) :
    GlobalTheory.Mem.UnitIndex.classHom E (localIdele E v x) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  classical
  have hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by simpa using v.ne_bot
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) =
      (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) := by
    refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_
    rw [GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w,
      FractionalIdeal.count_maximal]
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits
      (localIdele E v x) =
      FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
    Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])
  show ClassGroup.mk E _ = _
  rw [hu, ClassGroup.mk_mk0]

end GlobalTheory.IdeleClass

namespace GlobalTheory

theorem exists_ideleClassHom : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro E _ _
  refine ⟨GlobalTheory.Mem.UnitIndex.classHom E,
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl,
    sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)),
    fun v x hx => GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E
      (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hx),
    fun v x hx => GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hx⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

noncomputable section

namespace GlobalTheory.PstRank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def sigSt (g : ↥(GK K)) : Bst P ⊗[ℚ_[l]] V →ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] V :=
  TensorProduct.map (actSt P (g : GQ l)).toLinearMap ((ρ g).restrictScalars ℚ_[l])

theorem sigSt_smul (g : ↥(GK K)) (b : Bst P) (w : Bst P ⊗[ℚ_[l]] V) :
    sigSt P ρ g (b • w) = actSt P (g : GQ l) b • sigSt P ρ g w := by
  induction w using TensorProduct.inductionOn with
  | tmul c v => simp [sigSt, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem sigSt_comm (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P) :
    sigSt P ρ g (TensorProduct.comm ℚ_[l] V (Bst P) y) =
      TensorProduct.comm ℚ_[l] V (Bst P) (stRep P ρ g y) := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [sigSt]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem comm_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : V ⊗[ℚ_[l]] Bst P) :
    TensorProduct.comm ℚ_[l] V (Bst P) (mulV P LL V c y) = c • TensorProduct.comm ℚ_[l] V (Bst P) y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

def toB : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] Bst P ⊗[ℚ_[l]] V where
  toFun x := TensorProduct.comm ℚ_[l] V (Bst P) (((toUr P ρ).symm x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P)
  map_add' x y := by simp
  map_smul' c x := comm_mulV P c _

theorem toB_injective : Function.Injective (toB P ρ) := fun x y h =>
  (toUr P ρ).symm.injective (Subtype.ext ((TensorProduct.comm ℚ_[l] V (Bst P)).injective h))

end GlobalTheory.PstRank

namespace GlobalTheory.PstRank

theorem rank_DpstUr_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  intro l _ P hdom hreg K LL _ _ V _ _ _ _ _ ρ
  refine rank_le fun s hs => ?_
  choose F hF using fun i : ↥s => (mem_Dpst P ρ).mp ((toUr P ρ).symm (i : DpstUr P ρ)).2
  have hFd := fun i : ↥s => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let v : ↥s → Bst P ⊗[ℚ_[l]] V := fun i => toB P ρ (i : DpstUr P ρ)
  have hv : ∀ (g : ↥(GK K')) i, sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (v i) = v i := by
    intro g i
    change sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) v := hs.map' (toB P ρ) (LinearMap.ker_eq_bot.mpr (toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) v ((Finset.univ : Finset ↥s) : Set ↥s) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      v hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) v := by
    rw [← linearIndepOn_univ_iff]; rw [Finset.coe_univ] at hB; exact hB
  simpa using LinearIndependent.fintype_card_le_finrank hB'

end GlobalTheory.PstRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentatStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizerStatement
section
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)), haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) → ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | exact GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | (intros; apply GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalJumpSetsEqIntegerMultisetsTwistedDual
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem rat_jump_sets_eq_int_multisets : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  intro D i ρ g ep up hpl hup a
  have hP : hcAt D g = D.hc ρ := hcAt_eq_hc D ρ g hpl
  have hs : pos (if ep then 1 else -1) g = up := by
    unfold LJ.TypeU at hup
    rw [Formalism.HC.Frame.mem_Psi_iff] at hup
    rcases Int.units_eq_one_or g.1.2 with h | h <;> cases ep <;> cases up <;> simp_all [pos]
  have hsz : LJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (liftIdx D i) := by
    have := D.nd.j_range i
    unfold LJ.sz liftIdx
    rw [dite_eq_left (by omega)]
  have hc0 : LJ.c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  obtain ⟨h2, h1⟩ := jumps_rat (D.hc ρ) (liftIdx D i) up a
  rw [hP, hs, h1, h2]
  have hblk : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    refine exists_congr fun c => and_congr Iff.rfl ?_
    exact_mod_cast Iff.rfl
  have hblk' : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (D.R.t : ℚ) - 1 - (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    constructor
    · rintro ⟨c, hc, h⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      have h' : (D.R.t : ℤ) - 1 - x = c := by exact_mod_cast h
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      omega
    · rintro ⟨c, hc, rfl⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      ring
  cases up
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, Bool.false_eq_true, if_false, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk' (-a - 1)
    push_cast at this
    exact this
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, if_true, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk (-a - 1)
    push_cast at this
    exact this

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  first | exact @GlobalTheory.HTW.pageWord_Mi_add_hi_le | exact GlobalTheory.HTW.pageWord_Mi_add_hi_le | (intros; apply GlobalTheory.HTW.pageWord_Mi_add_hi_le <;> assumption)
end

