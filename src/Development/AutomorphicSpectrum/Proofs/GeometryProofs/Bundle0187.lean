module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit

section Lin

variable {Ω : Type} [Field Ω] {L : Type} [AddCommGroup L] [Module Ω L] {r : ℕ}

theorem exists_coeff_of_mem {c : Fin r → L} {s : Set (Fin r)} {x : L} (h : x ∈ Submodule.span Ω (c '' s)) :
    ∃ f : Fin r → Ω, (∀ j, j ∉ s → f j = 0) ∧ x = ∑ j, f j • c j := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp h
  refine ⟨l, fun j hj => ?_, ?_⟩
  · by_contra hne
    exact hj (hl (Finsupp.mem_support_iff.mpr hne))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

theorem coeff_unique {c : Fin r → L} (hc : LinearIndependent Ω c) {f g : Fin r → Ω}
    (h : ∑ j, f j • c j = ∑ j, g j • c j) (j : Fin r) : f j = g j := by
  have h0 : ∑ j, (f - g) j • c j = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have := Fintype.linearIndependent_iff.mp hc (f - g) h0 j
  rwa [Pi.sub_apply, sub_eq_zero] at this

theorem flag_change {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) :
    LinearIndependent Ω c ∧ ∀ i j, i < j → T i j = 0 := by
  have hr : ∀ v : Fin r → L, flagStep Ω v r = Submodule.span Ω (Set.range v) := by
    intro v
    show Submodule.span Ω (v '' {k : Fin r | (k : ℕ) < r}) = _
    rw [← Set.image_univ]
    congr 2
    ext k
    simp [k.isLt]
  have hc : LinearIndependent Ω c := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range c))
    rw [← hr c, ← hf r, hr b, finrank_span_eq_card hb]
  refine ⟨hc, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (c '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h1 : b i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    rw [hf] at h1
    exact h1
  obtain ⟨f, hf0, hfx⟩ := exists_coeff_of_mem hmem
  rw [coeff_unique hc ((hT i).symm.trans hfx) j]
  refine hf0 j (fun hj => ?_)
  have h2 : (i : ℕ) < j := hij
  have h3 : (j : ℕ) < (i : ℕ) + 1 := hj
  omega

theorem span_gr_eq (A : Subring Ω) {b c : Fin r → L} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b)
    (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (hT : ∀ i, b i = ∑ j, T i j • c j) (i : Fin r) :
    Submodule.span A {t : Ω | ∃ e ∈ Submodule.span A (Set.range b), e - t • c i ∈ flagStep Ω c i} =
      Submodule.span A {T i i} := by
  obtain ⟨hc, htri⟩ := flag_change hb hf hT
  have hterm : ∀ (v : Fin r → L) (g : Fin r → Ω), (∀ k, i < k → g k = 0) →
      ∑ k ∈ Finset.univ.erase i, g k • v k ∈ flagStep Ω v i := by
    intro v g hg
    refine Submodule.sum_mem _ fun k hk => ?_
    rcases lt_trichotomy k i with hki | hki | hki
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hki, rfl⟩)
    · exact absurd hki (Finset.ne_of_mem_erase hk)
    · rw [hg k hki, zero_smul]
      exact Submodule.zero_mem _
  have hbi : b i - T i i • c i ∈ flagStep Ω c i := by
    have := hterm c (fun j => T i j) (fun k hk => htri i k hk)
    rwa [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← hT i] at this
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, het⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp he
    set α : Fin r → Ω := fun k => (a k : Ω) with hα
    have hsum : ∑ k, a k • b k = ∑ k, α k • b k := rfl
    rw [hsum] at het
    have hci : c i ∈ flagStep Ω c ((i : ℕ) + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
    have hmono : flagStep Ω c i ≤ flagStep Ω c ((i : ℕ) + 1) :=
      Submodule.span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => Nat.lt_succ_of_lt hk)
    have he1 : ∑ k, α k • b k ∈ Submodule.span Ω (b '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
      have h1 : ∑ k, α k • b k ∈ flagStep Ω c ((i : ℕ) + 1) := by
        have := add_mem (hmono het) (Submodule.smul_mem _ t hci)
        rwa [sub_add_cancel] at this
      rw [← hf] at h1
      exact h1
    obtain ⟨f, hf0, hfe⟩ := exists_coeff_of_mem he1
    have hαz : ∀ k, i < k → α k = 0 := by
      intro k hk
      rw [coeff_unique hb hfe k]
      refine hf0 k (fun hk' => ?_)
      have h2 : (i : ℕ) < k := hk
      have h3 : (k : ℕ) < (i : ℕ) + 1 := hk'
      omega
    have hC : ∑ k, α k • b k - α i • b i ∈ flagStep Ω c i := by
      rw [← hf, ← Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      exact hterm b α hαz
    have hE : (α i * T i i - t) • c i ∈ flagStep Ω c i := by
      have heq : (α i * T i i - t) • c i =
          (∑ k, α k • b k - t • c i) - (∑ k, α k • b k - α i • b i) - α i • (b i - T i i • c i) := by
        rw [sub_smul, mul_smul, smul_sub]
        abel
      rw [heq]
      exact sub_mem (sub_mem het hC) (Submodule.smul_mem _ (α i) hbi)
    have ht : t = α i * T i i := by
      by_contra hne
      have hne' : α i * T i i - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hmem : c i ∈ flagStep Ω c i := by
        have := Submodule.smul_mem _ (α i * T i i - t)⁻¹ hE
        rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
      exact hc.notMem_span_image (s := {k : Fin r | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hmem
    rw [ht]
    exact Submodule.mem_span_singleton.mpr ⟨a i, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, hbi⟩

end Lin

section Lines

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem zpow_mem_span {A : Subring Ω} {s σ : Ω} (hs : s ≠ 0) (hσ : σ ≠ 0)
    (h : Submodule.span A {σ} = Submodule.span A {s}) (a : ℤ) : σ ^ a ∈ Submodule.span A {s ^ a} := by
  have h1 : σ ∈ Submodule.span A {s} := by
    rw [← h]
    exact Submodule.mem_span_singleton_self σ
  have h2 : s ∈ Submodule.span A {σ} := by
    rw [h]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.mp h2
  have hu' : (u : Ω) * s = σ := hu
  have hv' : (v : Ω) * σ = s := hv
  have huv : (u : Ω) * v = 1 := by
    have h3 : (u : Ω) * v * σ = 1 * σ := by rw [mul_assoc, hv', hu', one_mul]
    exact mul_right_cancel₀ hσ h3
  have hmem : ∀ n : ℤ, (u : Ω) ^ n ∈ A := by
    intro n
    rcases n with n | n
    · simpa using pow_mem u.2 n
    · have h4 : (u : Ω) ^ (Int.negSucc n) = (v : Ω) ^ (n + 1) := by
        rw [zpow_negSucc, ← inv_pow, inv_eq_of_mul_eq_one_right huv]
      rw [h4]
      exact pow_mem v.2 _
  rw [Submodule.mem_span_singleton]
  refine ⟨⟨(u : Ω) ^ a, hmem a⟩, ?_⟩
  show (u : Ω) ^ a * s ^ a = σ ^ a
  rw [← mul_zpow, hu']

theorem unit_of_tens (Λ : Lat ξ Ω) (q : Cpt ξ) (a : ℤ) {s M : Ω} (hs : Λ.IsGenAt q s) (hM0 : M ≠ 0)
    (hM : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q = Submodule.span (regAt ξ q) {M}) :
    M * s ^ (-a) ∈ regAt ξ q ∧ (M * s ^ (-a))⁻¹ ∈ regAt ξ q := by
  have hs0 : s ≠ 0 := hs.1
  have hsa : s ^ a ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    apply Submodule.subset_span
    exact ⟨fun _ => s, fun _ => hs, by simp⟩
  have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => a) q ≤ Submodule.span (regAt ξ q) {s ^ a} := by
    apply Submodule.span_le.mpr
    rintro t ⟨σ', hσ', rfl⟩
    have hσ := hσ' ()
    have heq : Submodule.span (regAt ξ q) {σ' ()} = Submodule.span (regAt ξ q) {s} := hσ.2.symm.trans hs.2
    simpa using zpow_mem_span hs0 hσ.1 heq a
  have hMmem : M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => a) q := by
    rw [hM]
    exact Submodule.mem_span_singleton_self M
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.mp (hle hMmem)
  rw [hM] at hsa
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsa
  have hr1 : (r' : Ω) * s ^ a = M := hr'
  have hr2 : (r : Ω) * M = s ^ a := hr
  have hsa0 : s ^ a ≠ 0 := zpow_ne_zero a hs0
  constructor
  · have h5 : M * s ^ (-a) = r' := by
      rw [← hr1, zpow_neg, mul_assoc, mul_inv_cancel₀ hsa0, mul_one]
    rw [h5]
    exact r'.2
  · have h6 : (M * s ^ (-a))⁻¹ = r := by
      rw [zpow_neg, mul_inv, inv_inv, ← hr2, mul_comm (r : Ω) M, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    rw [h6]
    exact r.2

end Lines

theorem root_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or ρ q ch hch b Tm hfl hfr hT hd
  have hL : (Or.Fl.rootLat ρ).IsDegOn Set.univ RM.y (RM.xdeg ρ) (Or.e ρ) := Or.lines ρ
  obtain ⟨_, hL2⟩ := hL
  have hdeg : Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q =
      Submodule.span (regAt Or.𝔐.ξ q) {(∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ} :=
    hL2 q (Set.mem_univ q) ch hch
  have hgr : ((Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2).IsGenAt q (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) := by
    refine ⟨hd _, ?_⟩
    have h1 := span_gr_eq (regAt Or.𝔐.ξ q) hfr.1 hfl hT (HodgeCpt.rootIdx Dw ρ).2
    rw [← hfr.2] at h1
    exact h1
  have hM0 : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ ≠ 0 := by
    intro h0
    have hmem : Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2 ^ HodgeCpt.rootSgn Dw ρ ∈
        Lat.tens (fun _ : Unit => (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).gr
          (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2) (fun _ => HodgeCpt.rootSgn Dw ρ) q := by
      apply Submodule.subset_span
      exact ⟨fun _ => Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2, fun _ => hgr, by simp⟩
    rw [hdeg, h0] at hmem
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hmem
    have hx' : (x : RM.Ω) * 0 = _ := hx
    rw [mul_zero] at hx'
    exact zpow_ne_zero _ (hd _) hx'.symm
  exact unit_of_tens _ q _ hgr hM0 hdeg

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianGenericIsoExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.CommonModel

section Ext

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B] {GK : Over (Sp K)} [GrpObj GK]

theorem hom_unique (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a) (g₁ g₂ : A ⟶ B) [IsMonHom g₁] [IsMonHom g₂]
    (h : a ≫ g₁.left = a ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  have hmap : (Over.pullback (spMap (algebraMap V K))).map g₂ =
      (Over.pullback (spMap (algebraMap V K))).map g₁ := by
    have L : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) =
          pullback.fst A.hom (spMap (algebraMap V K)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have R : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.snd B.hom (spMap (algebraMap V K)) =
          pullback.snd A.hom (spMap (algebraMap V K)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [L, L, ← hio, Category.assoc, Category.assoc, h]
    · rw [R, R]
  obtain ⟨F, -, hu⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    ((Over.pullback (spMap (algebraMap V K))).map g₁) inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap⟩).symm

theorem hom_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ F : A ⟶ B, IsMonHom F ∧ a ≫ F.left = b := by
  obtain ⟨io, hiom, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  obtain ⟨ko, -, hko⟩ := grpPullback_iso ha (isGrpPullback_pullback A (spMap (algebraMap V K)))
  obtain ⟨ko', hko'm, hko'⟩ := grpPullback_iso hb (isGrpPullback_pullback B (spMap (algebraMap V K)))
  have := hiom
  have := hko'm
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply ha.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨F, hFm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst A.hom (spMap (algebraMap V K)) ≫ F.left =
      ((Over.pullback (spMap (algebraMap V K))).map F).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hF, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem iso_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ a ≫ e.hom.left = b := by
  obtain ⟨F, hFm, hF⟩ := hom_exists V K hA hB ha hb
  obtain ⟨F', hF'm, hF'⟩ := hom_exists V K hB hA hb ha
  have := hFm
  have := hF'm
  have h₁ : F ≫ F' = 𝟙 _ := hom_unique V K hA hA ha _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF, hF', Over.id_left, Category.comp_id])
  have h₂ : F' ≫ F = 𝟙 _ := hom_unique V K hB hB hb _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF', hF, Over.id_left, Category.comp_id])
  exact ⟨⟨F, F', h₁, h₂⟩, hFm, hF⟩

end Ext

end GlobalTheory.CompanionTheory.Ar.CommonModel

namespace GlobalTheory.CompanionTheory.Ar

theorem semiAbelian_commonModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  intro V K _ _ _ _ _ _ X X' x x' G G' _ _ GK _ φ φ' hG hG' hφ hφ'
  have pA := isGrpPullback_pullback G x
  have pB := isGrpPullback_pullback G' x'
  have sA : IsSemiAbelian ((Over.pullback x).obj G) := IsSemiAbelian.pullback x G hG
  have sB : IsSemiAbelian ((Over.pullback x').obj G') := IsSemiAbelian.pullback x' G' hG'

  have lift : ∀ {Y : Scheme.{0}} (y : Sp V ⟶ Y) (H : Over Y) [GrpObj H] (θ : GK.left ⟶ H.left),
      IsGrpPullback GK H (spMap (algebraMap V K) ≫ y) θ →
      ∃ κ : GK.left ⟶ ((Over.pullback y).obj H).left,
        IsGrpPullback GK ((Over.pullback y).obj H) (spMap (algebraMap V K)) κ ∧
          κ ≫ pullback.fst H.hom y = θ := by
    intro Y y H _ θ hθ
    have hp := isGrpPullback_pullback H y
    have w : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ ((Over.pullback y).obj H).hom =
        GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
    have f : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ pullback.fst H.hom y = θ := hp.1.lift_fst _ _ _
    exact ⟨_, hp.cancel (by rw [f]; exact hθ) w, f⟩
  obtain ⟨κ, hκ, hκφ⟩ := lift x G φ hφ
  obtain ⟨κ', hκ', hκφ'⟩ := lift x' G' φ' hφ'
  obtain ⟨e, hem, he⟩ := CommonModel.iso_exists V K sA sB hκ hκ'
  have := hem
  refine ⟨(Over.pullback x).obj G, inferInstance, pullback.fst G.hom x,
    e.hom.left ≫ pullback.fst G'.hom x', κ, pA, ?_, hκ, hκφ, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp pB).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, he, hκφ']

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def tanW (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (w : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x) :
    Spec (CommRingCat.of (DualNumber S)) ⟶ Y.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ GlobalTheory.AllWt.ptF y) (by
    rw [hw, Category.assoc, GlobalTheory.AllWt.ptF, Limits.pullback.lift_fst]) ≫ Y.m.φ

theorem isComb_cast {V : Type} [CommRing V] {G : CategoryTheory.Over (Spec (CommRingCat.of V))} [GrpObj G] {r m : ℕ} (h : r = m)
    (v : Fin m → (epsOver V V ⟶ G)) (cf : Fin m → V) (w : epsOver V V ⟶ G) (hc : IsComb v cf w) :
    IsComb (fun i => v (Fin.cast h i)) (fun i => cf (Fin.cast h i)) w := by
  subst h
  exact hc

theorem spec_frac_ext (T : CDVR) {B : Type} [CommRing B]
    {p q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of T.Fr)}
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) : p = q := by
  rw [← Spec.map_preimage p, ← Spec.map_preimage q] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  congr 1
  ext1
  refine IsLocalization.ringHom_ext (nonZeroDivisors T.V) ?_
  exact congrArg CommRingCat.Hom.hom h2

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (T : CDVR)
    (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr)))
    (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (v : epsOver T.V T.V ⟶ G.G)
    (u' : Spec (CommRingCat.of (DualNumber T.Fr)) ⟶ t'.G.left)
    (h : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) := by
  apply spec_frac_ext T
  have e1 := m2.cart.1.w
  rw [Category.assoc, ← e1, ← Category.assoc, h, Category.assoc, Over.w v]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem diag_compare_of_triIn : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  intro V F EC _ _ _ _ _ _ _ r u v w a b d hu hv hw hb hd i
  classical
  obtain ⟨e, he⟩ :=
    (Submodule.mem_span_range_iff_exists_fun V).1 (hd (v i) (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨cv, hcvi, hcv0, hvi⟩ := hv i
  choose cw hcwd hcw0 hw' using hw
  have key : ∀ m, algebraMap V F d * cv m = ∑ j, algebraMap V F (e j) * cw j m := by
    have hL : d • v i = ∑ m, (algebraMap V F d * cv m) • u m := by
      rw [hvi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul, algebraMap_smul]
    have hR : ∑ j, e j • w j = ∑ m, (∑ j, algebraMap V F (e j) * cw j m) • u m := by
      simp_rw [hw', Finset.smul_sum, Finset.sum_smul, mul_smul, algebraMap_smul]
      exact Finset.sum_comm
    have h1 : ∑ m, (algebraMap V F d * cv m - ∑ j, algebraMap V F (e j) * cw j m) • u m = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← hL, ← hR, he, sub_self]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h1 m)
  have hzero : ∀ j, i < j → algebraMap V F (e j) = 0 := by
    by_contra hcon
    push_neg at hcon
    set S := Finset.univ.filter (fun j => i < j ∧ algebraMap V F (e j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hcon
      exact ⟨j, by simp [S, hj]⟩
    obtain ⟨J, hJS, hJmax⟩ : ∃ J ∈ S, ∀ j ∈ S, j ≤ J :=
      ⟨S.max' hS, S.max'_mem hS, fun j hj => S.le_max' j hj⟩
    have hJ : i < J ∧ algebraMap V F (e J) ≠ 0 := by simpa [S] using hJS
    have hmax : ∀ j, J < j → algebraMap V F (e j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by simp [S, hne, hJ.1.trans hj]
      exact not_le.2 hj (hJmax j hjS)
    have hk := key J
    rw [hcv0 J hJ.1, mul_zero, Finset.sum_eq_single J, hcwd J] at hk
    · exact hJ.2 ((mul_eq_zero.1 hk.symm).resolve_right (hb J))
    · intro j _ hjJ
      rcases lt_or_gt_of_ne hjJ with h | h
      · rw [hcw0 j J h, mul_zero]
      · rw [hmax j h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ J) h
  refine ⟨e i, ?_⟩
  have hk := key i
  rw [hcvi, Finset.sum_eq_single i, hcwd i] at hk
  · exact hk
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hcw0 j i h, mul_zero]
    · rw [hzero j h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

