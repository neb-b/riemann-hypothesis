module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevels
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.FixProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem rU_mul (x y : UA E a) (f : UA E a → ℂ) : RU E a (x * y) f = RU E a x (RU E a y f) := by
  rw [map_mul]; rfl

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU a w ≤ finU (E := E) (n := a) :=
  fun _ hx => (Subgroup.mem_inf.1 hx).1

theorem commute_of_apart {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) {x y : UA E a}
    (hx : x ∈ locU a w) (hy : y ∈ locU a u) : Commute x y := by
  show x * y = y * x
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hx, GlobalTheory.DefU.LocRet.mem_locU_inf hy]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have hv' : v.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E)) := hv ▸ h
      simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hy hv', one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hx hv, one_mul, mul_one]

section Avg

variable (K : Subgroup (UA E a)) (K' : Subgroup K) [Fintype (K ⧸ K')]

def avg : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ) :=
  ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a)

theorem avg_apply (f : UA E a → ℂ) :
    avg K K' f = ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a) f := by
  unfold avg
  exact LinearMap.sum_apply _ _ _

theorem avg_comm {c : UA E a} (hc : ∀ k ∈ K, Commute c k) (f : UA E a → ℂ) :
    avg K K' (RU E a c f) = RU E a c (avg K K' f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← rU_mul, ← rU_mul, (hc _ (Quotient.out q).2).eq]

theorem avg_of_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K, RU E a k f = f) :
    avg K K' f = (Fintype.card (K ⧸ K') : ℂ) • f := by
  rw [avg_apply, Finset.sum_congr rfl (fun q _ => hf _ (Quotient.out q).2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem avg_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K', RU E a ((k : K) : UA E a) f = f) (k : UA E a) (hk : k ∈ K) :
    RU E a k (avg K K' f) = avg K K' f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, map_sum]
  have key : ∀ q : K ⧸ K', RU E a k (RU E a ((Quotient.out q : K) : UA E a) f) =
      RU E a ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : UA E a) f := by
    intro q
    have hm : (Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (⟨k, hk⟩ : K) * Quotient.out q = Quotient.out ((⟨k, hk⟩ : K) • q) *
        ((Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q)) := (mul_inv_cancel_left _ _).symm
    have e' := congrArg (fun z : K => (z : UA E a)) e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at e'
    have hm' := hf _ hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hm'
    rw [← rU_mul, e', rU_mul, hm']
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun q => rfl)

end Avg

theorem mend (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (UA E a)) (hKw : K ≤ locU a w) (hKc : IsCompact (K : Set (UA E a)))
    {φw : UA E a → ℂ} (hφwU : φw ∈ U) (hφw0 : φw ≠ 0) (hφwK : ∀ k ∈ K, RU E a k φw = φw)
    {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0) :
    ∃ ψ ∈ U, ψ ≠ 0 ∧ (∀ k ∈ K, RU E a k ψ = ψ) ∧
      ∀ y : UA E a, (∀ x ∈ locU a w, Commute y x) → RU E a y φ = φ → RU E a y ψ = ψ := by
  classical

  let S := Submodule.span ℂ (Set.range fun g : UA E a => RU E a g φ)
  have hSU : S ≤ U := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hU.stable g φ hφU)
  have hSst : ∀ x, ∀ f ∈ S, RU E a x f ∈ S := by
    intro x f hf
    have : S ≤ S.comap (RU E a x) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU E a x (RU E a g φ) ∈ S
      rw [← rU_mul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact this hf
  have hφS : φ ∈ S := by
    have h1 : RU E a 1 φ = φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = U := by
    rcases hU.irred S hSU hSst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hφS)) hφ0
    · exact h
  have hφwS : φw ∈ S := hSeq ▸ hφwU
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφwS

  let r : UA E a → UA E a := fun g => (GlobalTheory.DefU.LocRet.ret w a g : UA E a)
  have hr : ∀ g, r g ∈ locU a w := fun g => (GlobalTheory.DefU.LocRet.ret w a g).2
  have hd : ∀ g, ∀ x ∈ locU a w, Commute ((r g)⁻¹ * g) x := fun g x hx =>
    GlobalTheory.DefU.LocRet.commute_ret g ⟨x, hx⟩
  have hsplit : ∀ g, RU E a g φ = RU E a ((r g)⁻¹ * g) (RU E a (r g) φ) := by
    intro g
    rw [← rU_mul, (hd g (r g) (hr g)).eq, mul_inv_cancel_left]

  have hKf : K ≤ finU (E := E) (n := a) := hKw.trans (locU_le_finU w)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let K' : Subgroup K :=
    { carrier := {k | ∀ g ∈ c.support, RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ}
      mul_mem' := fun {x y} hx hy g hg => by
        show RU E a ((x : UA E a) * (y : UA E a)) _ = _
        rw [rU_mul, hy g hg, hx g hg]
      one_mem' := fun g _ => by
        show RU E a 1 _ = _
        rw [map_one]; rfl
      inv_mem' := fun {x} hx g hg => by
        have h := hx g hg
        show RU E a ((x : UA E a)⁻¹) _ = _
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) (RU E a (r g) φ)) := by rw [h]
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hK'o : IsOpen (K' : Set K) := by
    have e : (K' : Set K) =
        ⋂ g ∈ c.support, {k : K | RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ} := by
      ext k
      rw [Set.mem_iInter₂]
      rfl
    rw [e]
    refine isOpen_biInter_finset fun g _ => ?_
    have ho := (hU.aut _ (hU.stable (r g) φ hφU)).level
    have hcont : Continuous fun k : K => (⟨(k : UA E a), hKf k.2⟩ : finU (E := E) (n := a)) :=
      continuous_subtype_val.subtype_mk _
    exact ho.preimage hcont
  haveI : Finite (K ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'o
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  have hA : avg K K' φw = c.sum fun g b => b • RU E a ((r g)⁻¹ * g) (avg K K' (RU E a (r g) φ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hsplit g, avg_comm K K' (fun k hk => hd g k (hKw hk))]
  by_cases h0 : ∀ g ∈ c.support, avg K K' (RU E a (r g) φ) = 0
  · exfalso
    have hz : avg K K' φw = 0 := by
      rw [hA, Finsupp.sum]
      exact Finset.sum_eq_zero fun g hg => by rw [h0 g hg, map_zero, smul_zero]
    rw [avg_of_fixed K K' hφwK] at hz
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    exact hφw0 ((smul_eq_zero.1 hz).resolve_left hcard)
  · push_neg at h0
    obtain ⟨g, hg, hne⟩ := h0
    refine ⟨avg K K' (RU E a (r g) φ), ?_, hne, ?_, ?_⟩
    · rw [avg_apply]
      exact Submodule.sum_mem _ fun q _ => hU.stable _ _ (hU.stable _ _ hφU)
    · exact avg_fixed K K' (fun k hk => hk g hg)
    · intro y hy hyφ
      rw [← avg_comm K K' (fun k hk => hy k (hKw hk)), ← rU_mul, (hy (r g) (hr g)).eq, rU_mul, hyφ]

theorem fix_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  intro E _ _ _ a U hU w₀ K hKl hKeq hKc hKint _ hφ'
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a (k : UA E a) φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        show RU E a ((x : UA E a) * (y : UA E a)) φ₀ = φ₀
        rw [rU_mul]
        exact (congrArg _ hy).trans hx
      one_mem' := by
        show RU E a 1 φ₀ = φ₀
        rw [map_one]; rfl
      inv_mem' := fun {x} hx => by
        show RU E a ((x : UA E a)⁻¹) φ₀ = φ₀
        have hx' : RU E a (x : UA E a) φ₀ = φ₀ := hx
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) φ₀) := by rw [hx']
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ₀ hφ₀U).level
  have hev := GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo
  have hgood : ∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, RU E a x φ₀ = φ₀ := by
    filter_upwards [hev, hKint] with w h1 h2 x hx
    exact h1 x (hKl w hx) (h2 x hx) (locU_le_finU w (hKl w hx))
  have hB := Filter.eventually_cofinite.1 hgood
  have main : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), ∃ φ ∈ U, φ ≠ 0 ∧ ∀ u, Apart u w₀ →
      ((∀ x ∈ K u, RU E a x φ₀ = φ₀) ∨ u ∈ S) → ∀ x ∈ K u, RU E a x φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨φ₀, hφ₀U, hφ₀, fun u _ hu x hx => ?_⟩
      rcases hu with hu | hu
      · exact hu x hx
      · exact absurd hu (Finset.notMem_empty u)
    | insert w S hwS ih =>
      obtain ⟨φ, hφU, hφ0, hφ⟩ := ih
      by_cases hw : Apart w w₀
      · obtain ⟨φw, hφwU, hφw0, hφwK⟩ := hφ' w hw
        obtain ⟨ψ, hψU, hψ0, hψK, hψy⟩ := mend U hU w (K w) (hKl w) (hKc w) hφwU hφw0 hφwK hφU hφ0
        refine ⟨ψ, hψU, hψ0, fun u hu hu' x hx => ?_⟩
        by_cases hap : Apart u w
        · refine hψy x (fun z hz => commute_of_apart hap (hKl u hx) hz) ?_
          rcases hu' with h | h
          · exact hφ u hu (Or.inl h) x hx
          · rcases Finset.mem_insert.1 h with rfl | h
            · exact absurd rfl hap
            · exact hφ u hu (Or.inr h) x hx
        · rw [hKeq u w hap] at hx
          exact hψK x hx
      · refine ⟨φ, hφU, hφ0, fun u hu hu' x hx => ?_⟩
        rcases hu' with h | h
        · exact hφ u hu (Or.inl h) x hx
        · rcases Finset.mem_insert.1 h with rfl | h
          · exact absurd hu hw
          · exact hφ u hu (Or.inr h) x hx
  obtain ⟨φ, hφU, hφ0, hφ⟩ := main hB.toFinset
  refine ⟨φ, hφU, hφ0, fun u hu x hx => hφ u hu ?_ x hx⟩
  by_cases h : ∀ x ∈ K u, RU E a x φ₀ = φ₀
  · exact Or.inl h
  · exact Or.inr (hB.mem_toFinset.2 h)

end GlobalTheory.Cong.FixProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.RepConj

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

theorem finrank_pi_card {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_pi_card, finrank_pi_card, h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

end GlobalTheory.AboveL.RepConj

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.RepConj

end GlobalTheory.AboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescent
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RealNormChar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp


open scoped GroundTheory.Global.AdeleBaseChange in
open GlobalTheory.UnitaryHeckeBaseChange in
theorem ideleNorm_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.GalOfCusp.ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hmap : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hmap, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  intro K M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield K) (maximalRealSubfield M) := (realHom K M).toAlgebra
  haveI : IsScalarTower (maximalRealSubfield K) (maximalRealSubfield M) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (maximalRealSubfield K) K M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨normChar (maximalRealSubfield M) χ,
    fun u => (normChar_locInf χ u (IsTotallyReal.isReal u)).trans (hsign _), fun x => ?_⟩
  show χ.1 (GroundTheory.Global.ideleNorm _ _ (GlobalTheory.GalOfCusp.ideleNorm M x)) =
    χ.1 (GlobalTheory.GalOfCusp.ideleNorm K (GroundTheory.Global.ideleNorm K M x))
  rw [ideleNorm_eq, ideleNorm_eq, GroundTheory.Global.ideleNorm_ideleNorm, GroundTheory.Global.ideleNorm_ideleNorm]

end GlobalTheory.RealNormChar

end
end

