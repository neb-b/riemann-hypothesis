module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaMod

open scoped Pointwise

variable {l : ℕ} [Fact l.Prime]

theorem ofGQ_apply (g : GQ l) (x : Om l) : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g x = g x := rfl

theorem Kur_stable (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  rw [← Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx ⊢
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_stable (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g) x hx
  rw [ofGQ_apply] at h
  exact h

theorem resid_of_fix (n : GQ l) (hn : ∀ x ∈ MaximalUnramifiedExtension l, n x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖n x - x‖ < 1 := by
  have hmem : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ n ∈
      ReciprocityTheory.DiscreteGroups.LocalClassField.subG l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
        (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)) := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_iff]
    intro x hx
    rw [Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx
    rw [ofGQ_apply]
    exact hn x hx
  intro x hx
  have h := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
    Formalism.MainNotions.N.PreambleDegrees.Loc.finiteDimensional_Q0_alt _).1 hmem x hx
  rw [ofGQ_apply] at h
  exact h

theorem fix_Kur_normal : ((MaximalUnramifiedExtension l).fixingSubgroup : Subgroup (GQ l)).Normal := by
  constructor
  intro n hn τ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (Kur_stable τ⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

theorem mem_IK_of_fix (σ : GQ l) (hσ : ∀ x ∈ MaximalUnramifiedExtension l, σ x = x) :
    ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (k' : GQ l) = σ := by
  have hG : σ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes a
  exact ⟨⟨σ, hG⟩, Subgroup.subset_closure (fun x hx => resid_of_fix σ hσ x hx), rfl⟩

theorem exists_fix_Kur (M : IntermediateField ℚ_[l] (Om l)) (g : GQ l)
    (hg : ∀ x ∈ M, x ∈ MaximalUnramifiedExtension l → g x = x) :
    ∃ h ∈ M.fixingSubgroup, ∀ x ∈ MaximalUnramifiedExtension l, (g * h) x = x := by
  haveI := fix_Kur_normal (l := l)
  let S : Subgroup (GQ l) := M.fixingSubgroup ⊔ (MaximalUnramifiedExtension l).fixingSubgroup
  have hSc : IsClosed (S : Set (GQ l)) := by
    rw [Subgroup.mul_normal]
    exact IsClosed.mul_left_of_isCompact (InfiniteGalois.fixingSubgroup_isClosed _)
      (InfiniteGalois.fixingSubgroup_isClosed M).isCompact
  have hfS : (IntermediateField.fixedField S).fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSc⟩
  have hgS : g ∈ S := by
    rw [← hfS, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply hg
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_right hσ)
  have hgNH : g ∈ ((M.fixingSubgroup : Set (GQ l)) * ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l))) := by
    rw [← Subgroup.mul_normal]; exact hgS
  obtain ⟨u, hu, n, hn, hun⟩ := Set.mem_mul.1 hgNH
  refine ⟨u⁻¹, M.fixingSubgroup.inv_mem hu, ?_⟩
  have hmem : g * u⁻¹ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    rw [← hun]
    exact (inferInstance : (MaximalUnramifiedExtension l).fixingSubgroup.Normal).conj_mem n hn u
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem

theorem seq_add_pow {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) : ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih =>
    show ϖ.seq (m + k + 1) ^ l ^ (k + 1) = _
    rw [pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem mem_level {a e : ℕ} [NeZero a] (ϖ : PiSys l e) {x : Om l} (hx : x ∈ ϖ.fieldInf a) :
    ∃ n, x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} := by
  let F : ℕ → IntermediateField ℚ_[l] (Om l) := fun n => Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n}
  have hs : ∀ n, ϖ.seq n ∈ F n := fun n =>
    (le_sup_right : _ ≤ F n) (IntermediateField.mem_adjoin_simple_self _ _)
  have hseq : ∀ m k, ϖ.seq m ∈ F (m + k) := by
    intro m k
    rw [← seq_add_pow ϖ m k]
    exact pow_mem (hs (m + k)) _
  have hmono : Monotone F := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact sup_le le_sup_left (IntermediateField.adjoin_simple_le_iff.2 (hseq m k))
  have hle : ϖ.fieldInf a ≤ ⨆ n, F n := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans le_sup_left (le_iSup F 0)
    · exact le_trans (IntermediateField.adjoin_simple_le_iff.2 (hs 0)) (le_iSup F 0)
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨n, rfl⟩
      exact le_iSup F n (hs n)
  have hx' : x ∈ ((⨆ n, F n : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hle hx
  rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hx'
  exact Set.mem_iUnion.1 hx'

theorem fix_Kunr {a : ℕ} [NeZero a] (g : GQ l) (hg : ∀ x : Om l, x ^ l ^ a = x → g x = x) :
    ∀ x ∈ Kunr l a, g x = x := fun x hx => by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hg x hx
  | algebraMap r => exact g.commutes r
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a →
    ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) →
      ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  intro l _ a e _ _ ϖ _ g hg
  obtain ⟨h, hh, hgh⟩ := exists_fix_Kur (ϖ.fieldInf a) g fun x hx hK => by
    obtain ⟨n, hn⟩ := mem_level ϖ hx
    exact fix_Kunr g hg x (_root_.GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup l a e ϖ n x hK hn)
  obtain ⟨k', hk', hkeq⟩ := mem_IK_of_fix (g * h) hgh
  exact ⟨k', hk', h, hh, hkeq⟩

end GlobalTheory.InertiaMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TripleFrobDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m i n : ℕ) (G : K⟦X⟧⟦X⟧) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * G)) = (m : K) * coeff n (coeff i G) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

theorem goodSet_of_finite_of_local (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hfin : ∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)),
      ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂)
    (hφ : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)))
    (hpow : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) :
    ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  classical
  rintro z ⟨w, rfl⟩
  have key : ∀ p : ℕ × ℕ, ∃ v b : Wq l a, ∀ τ : ZMod a,
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        algebraMap O K (emb t τ v) / (dpDen e p.1 p.2 : K) ∧
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        coeff p.2 (coeff p.1 ((ofW t K e w τ) ^ l)) +
          (l : K) * (algebraMap O K (emb t τ b) / (dpDen e p.1 p.2 : K)) := by
    rintro ⟨i, n⟩
    set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (n + 1) with hs
    obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hfin w s
    have hagree : ∀ τ : ZMod a, ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' (ofW t K e w τ)) =
        coeff n' (coeff i' (ofW t K e (fun p => if p ∈ s then w p else 0) τ)) := by
      intro τ i' hi n' hn
      have hm : (i', n') ∈ s := by
        simp only [hs, Finset.mem_product, Finset.mem_range]
        omega
      rw [coeff_ofW, coeff_ofW, if_pos hm]
    refine ⟨v (i, n), b (i, n), fun τ => ?_⟩
    have h1 : coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) =
        coeff n (coeff i (frob2 φ₂ (ofW t K e (fun p => if p ∈ s then w p else 0)) τ)) :=
      hφ i n _ _ (hagree (τ - 1))
    refine ⟨?_, ?_⟩
    · rw [h1, ← hv, coeff_ofW]
    · rw [h1, hB, hpow i n _ _ (hagree τ), Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
  choose v b hvb using key
  refine ⟨⟨w, rfl⟩, ⟨v, ?_⟩, ofW t K e b, ⟨b, rfl⟩, ?_⟩
  · funext τ
    ext i n
    rw [coeff_ofW]
    exact ((hvb (i, n) τ).1).symm
  · funext τ
    ext i n
    rw [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
    exact (hvb (i, n) τ).2

end GlobalTheory.CrysPrism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsDividedPowerSeriesGeneratorSet
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobTot_mem_SdSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  obtain ⟨w, hw, hF⟩ := hF
  have hpos : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨fun n => if l ∣ n then
      ((((n / e).factorial / ((n / l) / e).factorial : ℕ) : Wq l a) * sigma l a (w (n / l))) else 0, ?_, ?_⟩
  · intro r
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun m => l * m).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    split_ifs at hn with hd
    · refine ⟨n / l, ?_, Nat.mul_div_cancel' hd⟩
      intro hr
      apply hn
      obtain ⟨c, hc⟩ := hr
      exact Dvd.dvd.mul_left ⟨sigma l a c, by rw [hc, map_mul, map_pow, map_natCast]⟩ _
    · exact absurd (dvd_zero _) hn
  · intro τ n
    show _ = algebraMap O K (emb t τ (if l ∣ n then _ else 0))
    rw [frobTot_apply, coeff_frob]
    by_cases hd : l ∣ n
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left m hpos]
      have hdiv : (m / e).factorial ∣ (l * m / e).factorial :=
        Nat.factorial_dvd_factorial (Nat.div_le_div_right (Nat.le_mul_of_pos_left m hpos))
      rw [map_mul, map_natCast, emb_sigma, map_mul, map_natCast, ← hF (τ - 1) m, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdiv]
    · rw [if_neg hd, if_neg hd]; simp

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeries
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.FinSupp

section
variable {K : Type} [CommRing K]

def Bd (M : ℕ) (F : K⟦X⟧⟦X⟧) : Prop := ∀ i n, M < i ∨ M < n → coeff n (coeff i F) = 0

theorem Bd.mono {M M' : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) (hM : M ≤ M') : Bd M' F :=
  fun i n hin => h i n (by omega)

theorem Bd.mul {M M' : ℕ} {F G : K⟦X⟧⟦X⟧} (h : Bd M F) (h' : Bd M' G) : Bd (M + M') (F * G) := by
  intro i n hin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : M < p.1 ∨ M < q.1
  · rw [h _ _ h1, zero_mul]
  · rw [h' _ _ (by omega), mul_zero]

theorem bd_CC (c : K) : Bd 0 (C (C c) : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_C, if_neg (by omega)]
  · simp

theorem bd_CX : Bd 1 (C X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_X, if_neg (by omega)]
  · simp

theorem bd_X : Bd 1 (X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_X]
  split_ifs with h
  · rw [coeff_one, if_neg (by omega)]
  · simp


variable (K) in
def fin : Subring K⟦X⟧⟦X⟧ where
  carrier := {F | ∃ M, Bd M F}
  mul_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨_, h.mul h'⟩
  one_mem' := ⟨0, by simpa using bd_CC (1 : K)⟩
  add_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨M + M', fun i n hin => by
      rw [map_add (f := _), map_add (f := _), h i n (by omega), h' i n (by omega), add_zero]⟩
  zero_mem' := ⟨0, fun i n _ => by simp⟩
  neg_mem' := by
    rintro F ⟨M, h⟩
    exact ⟨M, fun i n hin => by rw [map_neg, map_neg, h i n hin, neg_zero]⟩

theorem Bd.eq_sum {M : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) :
    F = ∑ i ∈ Finset.range (M + 1), C (∑ n ∈ Finset.range (M + 1),
      C (coeff n (coeff i F)) * X ^ n) * X ^ i := by
  ext i n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum (coeff i), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hi : i < M + 1
  · simp only [if_pos hi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum (coeff n), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hn
    · rfl
    · exact h i n (by omega)
  · simp only [if_neg hi, map_zero]
    exact h i n (by omega)

theorem map_mem (φ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (h1 : ∀ c : K, φ (C (C c)) ∈ fin K)
    (h2 : φ (C X) ∈ fin K) (h3 : φ X ∈ fin K) {F : K⟦X⟧⟦X⟧} (hF : F ∈ fin K) : φ F ∈ fin K := by
  obtain ⟨M, h⟩ := hF
  rw [h.eq_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow]
  refine sum_mem fun i _ => mul_mem (sum_mem fun n _ => mul_mem (h1 _) (pow_mem h2 _)) (pow_mem h3 _)

theorem unif {ι : Type} [Finite ι] (F : ι → K⟦X⟧⟦X⟧) (h : ∀ τ, F τ ∈ fin K) : ∃ M, ∀ τ, Bd M (F τ) := by
  choose M hM using h
  obtain ⟨B, hB⟩ := (Set.finite_range M).bddAbove
  exact ⟨B, fun τ => (hM τ).mono (hB ⟨τ, rfl⟩)⟩

end

theorem exists_coeff_frob2_ofW_and_pow_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX N w hw
  have hF : ∀ τ, ofW t K e w τ ∈ fin K := fun τ => ⟨N, fun i n hin => by
    rw [coeff_ofW, hw i n hin]; simp⟩
  have hCX : (C X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_CX⟩
  have hX' : (X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_X⟩
  obtain ⟨M, hM⟩ := unif (frob2 φ₂ (ofW t K e w)) fun τ => by
    change φ₂ (ofW t K e w (τ - 1)) ∈ _
    refine map_mem φ₂ (fun c => ?_) ?_ ?_ (hF _)
    · have : frob K l (C c) = C c := (frob K l).commutes c
      rw [hC, this]; exact ⟨_, bd_CC c⟩
    · rw [hC, frob_X, map_pow]; exact pow_mem hCX _
    · rw [hX, map_pow]; exact sub_mem (pow_mem (add_mem hCX hX') _) (pow_mem hCX _)
  obtain ⟨M', hM'⟩ := unif (ofW t K e w ^ l) fun τ => pow_mem (hF τ) l
  exact ⟨M + M', fun τ i n hin => ⟨hM τ i n (by omega), hM' τ i n (by omega)⟩⟩

end GlobalTheory.CrysPrism.FinSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injOn_charValues_and_length_quotient : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  first | exact @GlobalTheory.CharValueLength.injOn_and_lenUnit | exact GlobalTheory.CharValueLength.injOn_and_lenUnit | (intros; apply GlobalTheory.CharValueLength.injOn_and_lenUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantLatticeFiltrationZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_lattice_filtration_zero :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
      [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
      [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l)
      (f : ZMod a → invL l (S O K e)),
      GlobalTheory.BKReal.PiSys.iB t K ϖ f ∈ GlobalTheory.BKGal.XiFil.filO O C 0 :=
  @GlobalTheory.BKGal.XiFil.iB_mem_filO_zero
end

