module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedSubfieldStableOfNormal
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Bridge

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem exists_finExt_of_open (U : Subgroup (Ω ≃ₐ[E] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[E] Ω))) :
    ∃ L : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK L → ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) ∈ U := by
  have hc : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : Gw) : Ω ≃ₐ[E] Ω) :=
    continuous_subtype_val.comp Bw.e_symm_cont
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 (hU.preimage hc)
  have h1 : (1 : GQ l) ∈ t := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      simp [U.one_mem]
    exact this
  obtain ⟨L, hL, hLt⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) t).1 (ht.mem_nhds h1)
  refine ⟨⟨L, hL⟩, fun g hg => ?_⟩
  have : g ∈ Subtype.val ⁻¹' t := hLt hg
  rw [hts] at this
  exact this

theorem rep_apply {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (g : ↥(GK Bw.Kw))
    (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

end Bridge

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

section Lat

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem toLL_mem (a : O) : Bw.toLL a ∈ OL Bw.LL := (Bw.eO a).2

theorem mem_stdG_OL {LL : FinExt l} {k : ℕ} (x : Fin k → ↥LL.1) :
    x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def bridgeLat {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K : FinExt l} (h : Bw.Kw.1 ≤ K.1) : LocLat ↥(GK K) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) where
  V := Fin m → ↥Bw.LL.1
  ρ := (Bw.rep r).comp (Subgroup.inclusion (GK_le h))
  cont := fun x => by
    have h1 : Continuous fun g : ↥(GK K) =>
        ((r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix.GeneralLinearGroup (Fin m) O) :
          Matrix (Fin m) (Fin m) O) :=
      hr.comp (Bw.e_symm_cont.comp (continuous_subtype_val.subtype_mk _))
    have h2 : Continuous (Bw.toLL) := continuous_subtype_val.comp Bw.eO_cont
    exact (h1.matrix_map h2).matrix_mulVec continuous_const
  L :=
    { T := stdG ↥(OL Bw.LL) ↥Bw.LL.1 m
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        simp only [MonoidHom.comp_apply, GlobalTheory.PotExt.rep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (toLL_mem Bw _) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective m))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥Bw.LL.1 (Fin m)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem isCrys_up (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (hr : Continuous fun g => ((r g : Matrix.GeneralLinearGroup (Fin m) O) : Matrix (Fin m) (Fin m) O))
    {K₁ K₂ : FinExt l} (h₁ : Bw.Kw.1 ≤ K₁.1) (h₁₂ : K₁.1 ≤ K₂.1)
    (hc : IsCrys ((LT l).PD K₁) ((Bw.rep r).comp (Subgroup.inclusion (GK_le h₁)))) :
    IsCrys ((LT l).PD K₂) ((Bw.rep r).comp (Subgroup.inclusion (GK_le (h₁.trans h₁₂)))) :=
  (hres l K₂ K₁ h₁₂ (GK_le h₁₂) Bw.LL (bridgeLat Bw r hr h₁) hc).1

end Lat

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

variable {l : ℕ} [Fact l.Prime]

theorem Kur_stable (σ : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : σ x ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (σ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem mem_of_normal {K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (σ : GQ l) {x : Om l} (hx : x ∈ K'.1) :
    σ x ∈ K'.1 :=
  IntermediateField.normal_iff_forall_map_le'.1 hn σ ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

theorem GKin_normal {K K' : FinExt l} (h : K.1 ≤ K'.1) (hn : Normal ℚ_[l] K'.1) : (GKin h).Normal := by
  haveI : IsGalois ℚ_[l] K'.1 := IsGalois.mk
  haveI : (GK K').Normal := (InfiniteGalois.normal_iff_isGalois K'.1).2 inferInstance
  unfold GKin
  infer_instance

theorem GKin_finiteIndex {K K' : FinExt l} (h : K.1 ≤ K'.1) : (GKin h).FiniteIndex := by
  haveI : Finite (GQ l ⧸ GK K') := Subgroup.quotient_finite_of_isOpen _ (@IntermediateField.fixingSubgroup_isOpen _ _ _ _ _ K'.1 K'.2)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  unfold GKin
  infer_instance

theorem maxUnramifiedSubfield_stable_of_normal (P : LocPrime l) {K K' : FinExt l} (hn : Normal ℚ_[l] K'.1) (g : ↥(GK K)) (c : ↥(K0 K')) :
    ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c' := by
  have hc1 : ((c : Om l)) ∈ K'.1 := c.2.1
  have hc2 : ((c : Om l)) ∈ MaximalUnramifiedExtension l := c.2.2
  refine ⟨⟨(g : GQ l) c, mem_of_normal hn _ hc1, Kur_stable _ hc2⟩, ?_⟩
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc2⟩ ⟨(g : GQ l) c, Kur_stable _ hc2⟩ rfl

end GlobalTheory.PotExt

namespace GlobalTheory.PotExt

theorem main : ∀ (D : D7) (P : Pend D), ElementDenominator.adm12 D → ∀ (i : D.nd.Loc) (k : Fin 2)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0) →
  ∀ (ι : Type) [Finite ι] (n : ℕ) (R : ι → (GE D.nd →* GL (Fin n) (D.nd.O i))) (n₀ : ℕ)
    (R₀ : GE D.nd →* GL (Fin n₀) (D.nd.O i)),
  (∀ j, Continuous fun g => ((R j g : GL (Fin n) (D.nd.O i)) : Matrix (Fin n) (Fin n) (D.nd.O i))) →
  (Continuous fun g => ((R₀ g : GL (Fin n₀) (D.nd.O i)) : Matrix (Fin n₀) (Fin n₀) (D.nd.O i))) →
  (∀ j, Br.IsPotCrysW D.loc D.nbr i w hw (R j)) → Br.IsPotCrysW D.loc D.nbr i w hw R₀ →
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
          algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
    (∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((R j).comp (decS D.nd w)))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R₀.comp (decS D.nd w))) ∧
    ∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
  intro D P hadm i k w hw Y hY ι _ n R n₀ R₀ hRc hR₀c hRp hR₀p
  unfold Br.IsPotCrysW LocBridge.IsPotCrysW at hRp hR₀p
  choose Kj hj hcj using hRp
  obtain ⟨K₀', h₀, hc₀⟩ := hR₀p
  have hLy : ∀ y : ↥Y, ∃ L : FinExt (D.nd.l i), ∀ g : ↥(GK (D.nbr i w hw).Kw), (g : GQ (D.nd.l i)) ∈ GK L →
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1 := by
    intro y
    obtain ⟨U, hU, hUo⟩ := P.om_open k w y (hY y y.2)
    obtain ⟨L, hL⟩ := exists_finExt_of_open (D.nbr i w hw) U hU
    exact ⟨L, fun g hg hI => hUo _ (hL g hg) hI⟩
  choose Ly hLy using hLy
  haveI : ∀ j, FiniteDimensional ℚ_[D.nd.l i] (Kj j).1 := fun j => (Kj j).2
  haveI : ∀ y, FiniteDimensional ℚ_[D.nd.l i] (Ly y).1 := fun y => (Ly y).2
  haveI := (D.nbr i w hw).Kw.2
  haveI := K₀'.2
  let M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    (D.nbr i w hw).Kw.1 ⊔ K₀'.1 ⊔ (⨆ j, (Kj j).1) ⊔ (⨆ y, (Ly y).1)
  haveI : FiniteDimensional ℚ_[D.nd.l i] M := by infer_instance
  let K' : FinExt (D.nd.l i) := ⟨IntermediateField.normalClosure ℚ_[D.nd.l i] M (Om (D.nd.l i)), inferInstance⟩
  have hMK : M ≤ K'.1 := IntermediateField.le_normalClosure M
  have hn : Normal ℚ_[D.nd.l i] K'.1 := normalClosure.normal _ _ _
  have h : (D.nbr i w hw).Kw.1 ≤ K'.1 := le_trans (le_sup_left.trans (le_sup_left.trans le_sup_left)) hMK
  have h0K : K₀'.1 ≤ K'.1 := le_trans (le_sup_right.trans (le_sup_left.trans le_sup_left)) hMK
  refine ⟨K', h, GKin_normal h hn, GKin_finiteIndex h, maxUnramifiedSubfield_stable_of_normal _ hn, fun j => ?_, ?_, ?_⟩
  · have hjK : (Kj j).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun j => (Kj j).1) j).trans (le_sup_right.trans le_sup_left)) hMK
    refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ ((hRc j).comp continuous_subtype_val) (hj j) hjK (hcj j)
  · refine (GlobalTheory.PcRes.main _ _ _ _ _ h _ _ _ _ _).2.2 ?_
    exact isCrys_up (D.nbr i w hw) D.loc hadm _ (hR₀c.comp continuous_subtype_val) h₀ h0K hc₀
  · intro y hy g hg hI
    have hyK : (Ly ⟨y, hy⟩).1 ≤ K'.1 :=
      le_trans ((le_iSup (fun y => (Ly y).1) ⟨y, hy⟩).trans le_sup_right) hMK
    exact hLy ⟨y, hy⟩ g (GK_le hyK (Subgroup.mem_subgroupOf.1 hg)) hI

end GlobalTheory.PotExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem multiset_eq_of_powerSums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 →
    (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ,
    (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  intro k _ _ z hz hroot J J' hsum

  have hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b := by
    intro a b hab heq
    have h1 : z ^ (b - a) = 1 := by
      rw [zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]
    have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [← h2, zpow_natCast] at h1
    exact hroot _ (by omega) h1
  have hinj : Function.Injective (fun h : ℤ => z ^ h) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab
    · exact hlt b a h hab.symm

  let χ : ℤ → (Multiplicative ℕ →* k) := fun h => powersHom k (z ^ h)
  have hχ : Function.Injective χ := (powersHom k).injective.comp hinj
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ
  rw [linearIndependent_iff'] at hli

  have key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k,
      (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h := by
    intro M s hs f
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    apply Finset.sum_subset hs
    intro x _ hx
    rw [Multiset.mem_toFinset] at hx
    simp [Multiset.count_eq_zero.mpr hx]
  set s : Finset ℤ := (J + J').toFinset with hs
  have hJ : J.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have hJ' : J'.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inr hx)
  have hzero := hli s (fun h => (J.count h : k) - (J'.count h : k)) (by
    funext m
    have e := hsum (Multiplicative.toAdd m)
    rw [key J s hJ, key J' s hJ'] at e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e)
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have := hzero a ha
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · rw [hs, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem polyDelta_supported_linear_mod (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ) :
    ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧
      ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i),
        (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  intro s hs
  have hX : ∀ (U : Set ℕ) (j : ℕ), j ∈ U → (MvPolynomial.X j : MvPolynomial ℕ A) ∈ MvPolynomial.supported A U :=
    fun U j hj => by
      rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨j, hj, rfl⟩
  have hC : ∀ (U : Subalgebra A (MvPolynomial ℕ A)) (a : A), MvPolynomial.C a ∈ U :=
    fun U a => U.algebraMap_mem a
  set S := MvPolynomial.supported A (Set.Iic i) with hS
  set T := MvPolynomial.supported A (Set.Iic (i + 1)) with hT
  have hST : S ≤ T := MvPolynomial.supported_mono (Set.Iic_subset_Iic.2 (Nat.le_succ i))
  have hcc : ∀ x y, x ∈ S → y ∈ S → cc l x y ∈ S := by
    intro x y hx hy
    unfold cc
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.pow_mem _ hx _))
      (Subalgebra.pow_mem _ hy _)
  have hS' : S = Algebra.adjoin A (MvPolynomial.X '' Set.Iic i) := MvPolynomial.supported_eq_adjoin_X _
  rw [hS'] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j ≤ i := Set.mem_Iic.1 hj
    rw [polyDelta_X]
    refine ⟨hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
    rcases Nat.lt_or_ge j i with h | h
    · refine ⟨0, Subalgebra.zero_mem _, MvPolynomial.X (j + 1), hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
      simp
    · have : j = i := le_antisymm hj' h
      subst this
      refine ⟨1, Subalgebra.one_mem _, 0, Subalgebra.zero_mem _, ?_⟩
      simp
  | algebraMap a =>
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨hC _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ a), hC _ _, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x + y) = (polyDelta D).δ x + (polyDelta D).δ y - cc l x y := (polyDelta D).δ_add x y
    rw [hd]
    refine ⟨T.sub_mem (T.add_mem hx1 hy1) (hST (hcc x y hx hy)), a1 + a2, S.add_mem ha1 ha2,
      b1 + b2 - cc l x y, S.sub_mem (S.add_mem hb1 hb2) (hcc x y hx hy), ?_⟩
    have := Ideal.add_mem _ hx2 hy2
    convert this using 1
    ring
  | mul x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x * y) = x ^ l * (polyDelta D).δ y + y ^ l * (polyDelta D).δ x +
        (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y := (polyDelta D).δ_mul x y
    rw [hd]
    refine ⟨T.add_mem (T.add_mem (T.mul_mem (T.pow_mem (hST hx) _) hy1) (T.mul_mem (T.pow_mem (hST hy) _) hx1))
        (T.mul_mem (T.mul_mem (T.natCast_mem _) hx1) hy1),
      x ^ l * a2 + y ^ l * a1, S.add_mem (S.mul_mem (S.pow_mem hx _) ha2) (S.mul_mem (S.pow_mem hy _) ha1),
      x ^ l * b2 + y ^ l * b1, S.add_mem (S.mul_mem (S.pow_mem hx _) hb2) (S.mul_mem (S.pow_mem hy _) hb1), ?_⟩
    have h3 : (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y ∈
        Ideal.span {(l : MvPolynomial ℕ A)} :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (x ^ l) hy2) (Ideal.mul_mem_left _ (y ^ l) hx2)) h3
    convert this using 1
    ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ScalarFrob

section HidaSetting

open IsLocalRing GlobalTheory.TwistDet GlobalTheory.PrimeToInertia

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem natCast_eq_one_of_mod {q : ℕ} (hq : q % X.l i = 1) : (q : ResidueField (X.O0 i)) = 1 := by
  have hl : ((X.l i : ℕ) : ResidueField (X.O0 i)) = 0 := by
    rw [← map_natCast (residue (X.O0 i)), (residue_eq_zero_iff _).2 (l_mem i)]
  rw [← Nat.mod_add_div q (X.l i), hq]
  push_cast
  rw [hl]
  simp

theorem frob_scalar_place (bkP : BKPh X) (h : GalHyp bkP i s) {P : PlE D.host} {z : GE N} {L : Subgroup (GE N)}
    (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : Small i s L z) (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 (natCast_eq_one_of_mod i hp.2) hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 (natCast_eq_one_of_mod i hp0.2) hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

end HidaSetting


open GlobalTheory.PrimeToInertia in
theorem firstPlace : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstPlace i s := by
  intro h1 h2 h3 D N X bkP i s h P z L hz hL hA hS Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ v hv
  have hp := hA v hv
  have hq := natCast_eq_one_of_mod i hp.2
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
  obtain ⟨c, c0, c1, hc⟩ := frob_scalar_place i s bkP h hz hL hA hS hv hσ
  obtain ⟨c', c1', hc'⟩ : ∃ c' : IsLocalRing.ResidueField (X.O0 i), c' ≠ 1 ∧
      ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) = c' • 1 := by
    rcases hρ with rfl | hρ
    · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
    · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i hp.1 hq hσ) c0 hc]⟩
  have hcont : Continuous fun g => ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
    rcases hρ with rfl | hρ
    · simp_rw [Tgl_coe]; exact continuous_Tmat i s
    · simp_rw [show ∀ g, _ = _ from hρ]; exact continuous_Tdual i s
  refine primary_case (l := X.l i) h1 h2 h3 (N.plOm.2 v) (fun h => hp.1 (X.twistExcludedPlaces_contains_residueChar i h)) _
    ?_ (fun m => ?_) ⟨σ, hσ.1⟩ hσ (fun m hm => ?_) (fun m hm => ?_)
  · exact (contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ hcont κ hκ hB).comp
      (f := fun p : DecV N v × (Fin D.R.r → B) => ((p.1 : GE N), p.2)) (by fun_prop)
  · obtain ⟨n, hn⟩ := exists_pow_kill hB m
    refine ⟨n, funext fun a => ?_⟩
    have := hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow (l_mem i) n)) a
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' hq m hm

end GlobalTheory.ScalarFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMap
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ringHom_eq_of_isCompl (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C) (hc : IsCompl i J) (hH : IsHausdorff JC C)
    (h h' : Q →+* C) (hJ : J.map (h.comp i) ≤ JC) (he : h.comp i = h'.comp i) : h = h' := by
  have mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n := by
    intro g hg n y hy
    have h1 : g y ∈ ((J ^ n).map i).map g := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hg n h1
  have hJ' : J.map (h'.comp i) ≤ JC := by rwa [← he]
  ext x
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha⟩ := hc.surj x n
  have e1 : h x - h' x = h (x - i a) - h' (x - i a) := by
    have : h (i a) = h' (i a) := RingHom.congr_fun he a
    simp only [map_sub, this]; ring
  rw [SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)

end GlobalTheory.BSP
end

