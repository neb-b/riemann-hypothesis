module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulEqAcrisLatticeImage
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DenomCris

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem cc_one : WittVector.constantCoeff (1 : Ainf l) ≠ 0 := by
  obtain ⟨e, -, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI : Nontrivial (Per.Fl l) := ⟨e, 1, hne⟩
  rw [map_one]
  exact one_ne_zero

theorem cc_mul {x y : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (hy : WittVector.constantCoeff y ≠ 0) :
    WittVector.constantCoeff (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem cc_pow {x : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (n : ℕ) :
    WittVector.constantCoeff (x ^ n) ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact cc_one
  | succ n ih => rw [pow_succ]; exact cc_mul ih hx

theorem exists_mul_eq_toOB (r : OB l O) : ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ a : OCr l O,
    ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) * r = toOB l O a := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul o y =>
    obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
    obtain ⟨n, a, ha⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne y
    refine ⟨(Per.tm e - 1) ^ n, cc_pow (GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne) n, o ⊗ₜ a, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change o ⊗ₜ[ℤ_[l]] (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Ainf l) (Per.Acris l) ((Per.tm e - 1) ^ n)) * y) =
      o ⊗ₜ[ℤ_[l]] algebraMap (Per.Acris l) (Per.Bcris l) a
    rw [map_pow, map_pow, mul_comm, ha]
  | add r₁ r₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) * a₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) * a₂, ?_⟩
    have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
        (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hm, map_add (f := _), map_mul (toOB l O), map_mul (toOB l O), hc, hc, ← e₁, ← e₂]
    ring

theorem exists_smul_eq_TWincl : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  intro l _ O K _ _ _ _ _ _ G _ _ T b
  have hsm : ∀ (r : OCr l O) (z : TW (OCr l O) T),
      TWincl (toOB l O) T (r • z) = toOB l O r • TWincl (toOB l O) T z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x t => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), h₁, h₂, map_add (f := _), smul_add]
  have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
      (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul r t =>
    obtain ⟨s, hs, a, e⟩ := exists_mul_eq_toOB r
    exact ⟨s, hs, a ⊗ₜ t, by rw [TensorProduct.smul_tmul', smul_eq_mul, e]; rfl⟩
  | add b₁ b₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, β₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, β₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) • β₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) • β₂, ?_⟩
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) *
          ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [map_add (f := _), hsm, hsm, hc, hc, ← e₁, ← e₂, smul_smul, smul_smul, hm, smul_add, mul_comm (_ ⊗ₜ[ℤ_[l]] _)]

end GlobalTheory.DenomCris
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.FrobGen
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem exists_gen_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) [J.Normal] (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hg : (Subgroup.zpowers g ⊔ J).topologicalClosure = ⊤) :
    ∃ φ : U, (Subgroup.zpowers φ ⊔ J.subgroupOf U).topologicalClosure = ⊤ := by
  let π : G →* G ⧸ J := QuotientGroup.mk' J
  let S : AddSubgroup ℤ :=
    { carrier := {n | π g ^ n ∈ U.map π}
      add_mem' := fun {a b} ha hb => by
        show π g ^ (a + b) ∈ U.map π
        rw [zpow_add]; exact mul_mem ha hb
      zero_mem' := by
        show π g ^ (0 : ℤ) ∈ U.map π
        rw [zpow_zero]; exact one_mem _
      neg_mem' := fun {a} ha => by
        show π g ^ (-a) ∈ U.map π
        rw [zpow_neg]; exact inv_mem ha }
  obtain ⟨f, hf⟩ := S.isAddCyclic_iff_exists_zmultiples_eq.mp S.isAddCyclic
  have hf : S = AddSubgroup.closure {f} := by rw [← hf, AddSubgroup.zmultiples_eq_closure]
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨φ, hφU, hφ⟩ : π g ^ f ∈ U.map π := hfS
  refine ⟨⟨φ, hφU⟩, ?_⟩
  have hd : Dense ((Subgroup.zpowers g ⊔ J : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hg, Subgroup.coe_top]
  have hd2 := hd.preimage (f := (Subtype.val : U → G)) hU.isOpenMap_subtype_val
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]
  refine hd2.mono fun y hy => ?_
  have h1 : π y ∈ (Subgroup.zpowers g ⊔ J).map π := ⟨y, hy, rfl⟩
  have h2 : J.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, h2, sup_bot_eq, MonoidHom.map_zpowers] at h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hnS : n ∈ S := by
    show π g ^ n ∈ U.map π
    rw [hn]; exact ⟨y, y.2, rfl⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at hnS
  obtain ⟨k, rfl⟩ := hnS
  have h3 : π ((φ ^ k)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_zpow, hφ, ← hn, ← zpow_mul, smul_eq_mul, mul_comm f k, inv_mul_cancel]
  have h4 : (φ ^ k)⁻¹ * (y : G) ∈ J := by
    rw [← QuotientGroup.ker_mk' J]; exact h3
  have h5 : y = (⟨φ, hφU⟩ : U) ^ k * ((((⟨φ, hφU⟩ : U) ^ k))⁻¹ * y) := by
    rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, h5]
  refine Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) ?_
  rw [Subgroup.mem_subgroupOf]
  simpa using h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_mem_Kur {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

theorem normal_fix : (MaximalUnramifiedExtension l).fixingSubgroup.Normal := by
  refine ⟨fun σ hσ h => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨m, hm, hlm, H⟩ := exists_level hx
  refine H _ 1 fun ζ hζ => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    hσ _ (root_mem_Kur hm hlm (by rw [← map_pow, hζ, map_one])), ← AlgEquiv.mul_apply,
    mul_inv_cancel]

theorem norm_sub_lt {σ : GQ l} (hσ : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖σ x - x‖ < 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have := key _ hn
    rw [map_sub, hσ ζ (root_mem_Kur hm hlm hζ)] at this
    simpa using this

theorem exists_gen_top :
    ∃ g : GQ l, (Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure = ⊤ := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  let H : ClosedSubgroup (GQ l) :=
    ⟨(Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩
  have h1 := InfiniteGalois.fixingSubgroup_fixedField H
  have h2 : IntermediateField.fixedField (H : Subgroup (GQ l)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hf))
    have hgx : g x = x := hx g (Subgroup.le_topologicalClosure _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))
    obtain ⟨c, hc⟩ := (frob_laws l σ hσ).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hgx))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  rw [h2, IntermediateField.fixingSubgroup_bot] at h1
  exact h1.symm

end GlobalTheory.FrobGen

theorem GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    ∃ φ : ↥(GK K), (Subgroup.zpowers φ ⊔ IK K).topologicalClosure = ⊤ := by
  obtain ⟨g, hg⟩ := GlobalTheory.FrobGen.exists_gen_top (l := l)
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  haveI := K.2
  obtain ⟨φ, hφ⟩ := GlobalTheory.FrobGen.exists_gen_of_isOpen _ g (GK K) K.1.fixingSubgroup_isOpen hg
  refine ⟨φ, eq_top_iff.2 (hφ ▸ ?_)⟩
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)
  refine le_trans (sup_le_sup_left (fun σ hσ => ?_) _) (Subgroup.le_topologicalClosure _)
  exact Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hσ x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundame
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

noncomputable section

namespace GlobalTheory.CellDec.RatUnip

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem row_mul_split (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (r : Fin n → E) (j : Fin n) :
    ∑ k, algebraMap E (Ad E) (r k) * w k j =
      (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) + algebraMap E (Ad E) (r j) := by
  have key : ∀ k, algebraMap E (Ad E) (r k) * w k j =
      (if k < j then algebraMap E (Ad E) (r k) * w k j else 0) +
        (if j = k then algebraMap E (Ad E) (r k) else 0) := by
    intro k
    rcases lt_trichotomy k j with h | rfl | h
    · simp [h, h.ne']
    · simp [hd]
    · simp [not_lt.2 h.le, h.ne, hl k j h]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem row_unique (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) (r r' : Fin n → E)
    (h0 : ∀ k, k < i → r k = 0) (h0' : ∀ k, k < i → r' k = 0) (h1 : r i = 1) (h1' : r' i = 1)
    (hF : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E)
    (hF' : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r' k) * w k j ∈ GroundTheory.Global.fundamentalSet E) :
    r = r' := by
  suffices h : ∀ m : ℕ, ∀ j : Fin n, j.val < m → r j = r' j from
    funext fun j => h _ j j.val.lt_succ_self
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact ih j hj
    rcases lt_trichotomy j i with h | rfl | h
    · rw [h0 j h, h0' j h]
    · rw [h1, h1']
    · have hs : (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) =
          ∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [ih k (by have := Fin.lt_def.1 hk; omega)]
        · rfl
      have a := hF j h
      have b := hF' j h
      rw [row_mul_split w hl hd] at a b
      rw [hs] at a
      obtain ⟨c, -, hc⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0)
      have e1 := hc (-r j) (by simpa using a)
      have e2 := hc (-r' j) (by simpa using b)
      exact neg_injective (e1.trans e2.symm)

theorem row_exists (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) :
    ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E := by
  suffices h : ∀ m : ℕ, ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j : Fin n, i < j → j.val < m →
        ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E by
    obtain ⟨r, h0, h1, h2⟩ := h n
    exact ⟨r, h0, h1, fun j hj => h2 j hj j.isLt⟩
  intro m
  induction m with
  | zero =>
    exact ⟨Pi.single i 1, fun k hk => by simp [Pi.single_apply, hk.ne], by simp,
      fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨r, h0, h1, h2⟩ := ih
    by_cases hm : ∃ jm : Fin n, jm.val = m ∧ i < jm
    · obtain ⟨jm, hjm, hijm⟩ := hm
      obtain ⟨c, hc, -⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, algebraMap E (Ad E) (r k) * w k jm)
      refine ⟨r - Pi.single jm c, fun k hk => ?_, ?_, fun j hij hj => ?_⟩
      · simp [h0 k hk, Pi.single_apply, (hk.trans hijm).ne]
      · simp [h1, Pi.single_apply, hijm.ne]
      · have hsum : ∑ k, algebraMap E (Ad E) ((r - Pi.single jm c : Fin n → E) k) * w k j =
            ∑ k, algebraMap E (Ad E) (r k) * w k j - algebraMap E (Ad E) c * w jm j := by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          congr 1
          rw [Finset.sum_eq_single jm]
          · simp
          · intro k _ hk; simp [Pi.single_apply, hk]
          · simp
        rw [hsum]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · have hlt : j < jm := by rw [Fin.lt_def]; omega
          rw [hl jm j hlt, mul_zero, sub_zero]
          exact h2 j hij hj
        · have : j = jm := Fin.ext (hj.trans hjm.symm)
          subst this
          rw [hd, mul_one]; exact hc
    · refine ⟨r, h0, h1, fun j hij hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact h2 j hij hj
      · exact absurd ⟨j, hj, hij⟩ hm

end GlobalTheory.CellDec.RatUnip

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.RatUnip

theorem existsUnique_ratUnip_mul_mem_fundamentalSet (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n)
    (hu : u ∈ GlobalTheory.CellDec.NA E n) :
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hent : ∀ (γ : GL (Fin n) E) (i j : Fin n),
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
        ∑ k, algebraMap E (Ad E) ((γ : Matrix (Fin n) (Fin n) E) i k) * (u : Matrix (Fin n) (Fin n) (Ad E)) k j := by
    intro γ i j
    simp [ratGL, Matrix.mul_apply]
  choose r h0 h1 hF using row_exists (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => r i k
  have hM : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular (show M.BlockTriangular id from fun i j hij => h0 i j hij)]
    simp [M, h1]
  refine ⟨Matrix.nonsingInvUnit M hM,
    ⟨(GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => h0 i j hij, fun i => h1 i⟩, fun i j hij => ?_⟩, ?_⟩
  · rw [hent]; exact hF i j hij
  · rintro γ ⟨hγ, hγF⟩
    obtain ⟨gl, gd⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
    apply Units.ext
    ext i j
    have := row_unique (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd i
      (fun k => (γ : Matrix (Fin n) (Fin n) E) i k) (r i) (fun k hk => gl i k hk) (h0 i) (gd i) (h1 i)
      (fun j hij => by rw [← hent]; exact hγF i j hij) (hF i)
    exact congrFun this j

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperUnitriangularEntriesHomeomorph
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.UnipCoords

variable (R : Type) [CommRing R] (n : ℕ)

def strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then x ⟨(i, j), h⟩ else 0

theorem det_one_add_strictUpper (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (1 + strictUpper R n x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [strictUpper]
  · intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [strictUpper, h1, h2, Matrix.one_apply_ne h2]

def unitOf (x : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R where
  val := 1 + strictUpper R n x
  inv := (1 + strictUpper R n x).adjugate
  val_inv := by rw [Matrix.mul_adjugate, det_one_add_strictUpper, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, det_one_add_strictUpper, one_smul]

theorem unitOf_mem (x : {p : Fin n × Fin n // p.1 < p.2} → R) :
    unitOf R n x ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h1 : ¬ i < j := not_lt.2 (le_of_lt hji)
    have h2 : i ≠ j := ne_of_gt hji
    simp [unitOf, strictUpper, h1, Matrix.one_apply_ne h2]
  · simp [unitOf, strictUpper]

end GlobalTheory.UnipCoords

open GlobalTheory.UnipCoords in
theorem GlobalTheory.UnipCoords.unipCoordsHomeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  intro R _ _ _ n
  have hX : Continuous (fun x : {p : Fin n × Fin n // p.1 < p.2} → R => strictUpper R n x) := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i < j
    · simp only [strictUpper, Matrix.of_apply, h, dite_true]; exact continuous_apply _
    · simp only [strictUpper, Matrix.of_apply, h, dite_false]; exact continuous_const
  let e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    { toFun := fun u p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
      invFun := fun x => ⟨unitOf R n x, unitOf_mem R n x⟩
      left_inv := by
        rintro ⟨u, hu⟩
        obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
        apply Subtype.ext; apply Units.ext; ext i j
        change (1 + strictUpper R n _) i j = _
        rcases lt_trichotomy i j with h | h | h
        · simp [strictUpper, h, Matrix.one_apply_ne (ne_of_lt h)]
        · subst h; simp [strictUpper, h2]
        · have h' : ¬ i < j := not_lt.2 (le_of_lt h)
          simp [strictUpper, h', Matrix.one_apply_ne (ne_of_gt h), h1 i j h]
      right_inv := by
        intro x; funext p
        change (1 + strictUpper R n x) p.1.1 p.1.2 = x p
        simp [strictUpper, p.2, Matrix.one_apply_ne (ne_of_lt p.2)] }
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, fun u => rfl⟩
  · refine continuous_pi fun p => ?_
    have hv : Continuous (fun u : GlobalTheory.SmGL.unipB R (Fin n) => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
    exact (continuous_apply_apply p.1.1 p.1.2).comp hv
  · refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_const.add hX
    · exact (continuous_const.add hX).matrix_adjugate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulMinpolyNatDegreeLeOfPowEqNeg
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


open IntermediateField in
theorem GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  intro l _ F N x hN hx hF
  have hp : (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])).Monic :=
    Polynomial.monic_X_pow_add_C _ hN.ne'
  have hroot : Polynomial.aeval x (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])) = 0 := by simp [hx]
  have hint : IsIntegral ℚ_[l] x := ⟨_, hp, hroot⟩
  have hdeg : (minpoly ℚ_[l] x).natDegree ≤ N := by
    have h1 := minpoly.min ℚ_[l] x hp hroot
    rw [Polynomial.degree_X_pow_add_C hN] at h1
    exact Polynomial.natDegree_le_of_degree_le h1
  have hintF : IsIntegral F x := hint.tower_top
  have key := Module.finrank_mul_finrank ℚ_[l] F (F⟮x⟯)
  have hE : (F⟮x⟯).restrictScalars ℚ_[l] = ℚ_[l]⟮x⟯ := by
    rw [restrictScalars_adjoin]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact hF hy
      · rw [Set.mem_singleton_iff.mp hy]; exact mem_adjoin_simple_self _ _
    · exact adjoin.mono _ _ _ (Set.subset_union_right)
  have h2 : Module.finrank ℚ_[l] (F⟮x⟯) = Module.finrank ℚ_[l] (ℚ_[l]⟮x⟯) := by
    rw [← hE]; rfl
  rw [← adjoin.finrank hintF, key, h2, adjoin.finrank hint]
  exact hdeg
end

