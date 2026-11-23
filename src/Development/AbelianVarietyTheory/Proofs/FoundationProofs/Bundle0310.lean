module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralEqSumOfSurjective
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassUnfold

theorem integral_eq_sum_of_surjective {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (I : Type) [Fintype I] (y : I → H)
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (hf : ∀ c, Finite (Bridge.stab (π.comp Γ.subtype) J (y c)))
    (Φ : H → ℂ) (hΦ : ∀ (γ : Γ) h (k : J), Φ (π.comp Γ.subtype γ * h * k) = Φ h) :
    ∫ h in 𝓖, Φ (π h) ∂ν = ∑ c, (Nat.card (Bridge.stab (π.comp Γ.subtype) J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  choose h hh using fun c => hπ (y c)
  have hS : ∀ c, {γ : G | γ ∈ Γ ∧ (h c)⁻¹ * γ * h c ∈ J.comap π} =
      Subtype.val '' (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab, Subgroup.mem_comap, map_mul,
      map_inv, hh]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨⟨γ, a⟩, b, rfl⟩
    · rintro ⟨δ, b, rfl⟩
      exact ⟨δ.2, b⟩
  have hfin : ∀ c, (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ).Finite := fun c => hf c
  have key := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (by rw [h1]; exact ENNReal.one_ne_top) I h ?_ (fun c => by rw [hS]; exact (hfin c).image _)
    (fun x => Φ (π x)) ?_ ?_
  · rw [key.2.2, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Set.ncard_image_of_injective _ Subtype.val_injective, hh]
    rfl
  · intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * h i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hh, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, hh]; rfl⟩
  · intro γ hγ x
    have := hΦ ⟨γ, hγ⟩ (π x) 1
    rw [OneMemClass.coe_one, mul_one] at this
    rw [map_mul]
    exact this
  · intro k hk x
    have := hΦ 1 (π x) ⟨π k, hk⟩
    rw [map_one, one_mul] at this
    rw [map_mul]
    exact this

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), L.P.H = ⊥ → IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 → ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y → (∀ c, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c))) → ∀ Φ : Bridge.Gf V → ℂ, (∀ (γ : GQ V) h (k : (levEnv V β L).J), Φ (Bridge.ratF V γ * h * k) = Φ h) → ∫ h in 𝓕, Φ (fin V h) ∂μ = ∑ c, (Nat.card (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  intro D V β L μ 𝓕 hL hμ I _ y hy hf Φ hΦ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hμ.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (finE V) := by
    ext g
    change (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ (⊥ : Subgroup _)) ↔
      (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ L.P.H)
    rw [hL]
  refine integral_eq_sum_of_surjective μ (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J 𝓕 hμ.2 ?_ ?_ I y hy hf Φ hΦ
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1

end GlobalTheory.ClassUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTensorOfIntegrable
section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField IsDedekindDomain
open GlobalTheory.AutomorphicL2Unitary (conv)

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsFullLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
  {μ : Measure (GAd σ J)} {fa fa' : ∀ w, GArch σ J w → ℂ} {ff ff' : ∀ v, GLoc σ J v → ℂ}


omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem unitLoc_mul_translate {v : HeightOneSpectrum (𝓞 F)} {y : GLoc σ J v} (hy : y ∈ stabLoc σ J L v) :
    (fun x => unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y)) = unitLoc σ J L v := by
  funext x
  by_cases hx : x ∈ stabLoc σ J L v
  · simp [unitLoc, hx, mul_mem (inv_mem hx) hy]
  · simp [unitLoc, hx]

theorem conv_unitLoc {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (GLoc σ J v)) :
    conv ν (unitLoc σ J L v) (unitLoc σ J L v) = (ν.real (stabLoc σ J L v) : ℂ) • unitLoc σ J L v := by
  funext y
  by_cases hy : y ∈ stabLoc σ J L v
  · rw [conv, unitLoc_mul_translate hy, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Pi.smul_apply, indicator_of_mem hy, Complex.real_smul]
    rfl
  · have : ∀ x, unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ stabLoc σ J L v
      · simp [unitLoc, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
      · simp [unitLoc, hx]
    rw [conv]
    simp only [this, integral_zero]
    simp [unitLoc, hy]

theorem IsFinFamily.conv (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff')
    (h1 : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) : IsFinFamily σ J L fun v => conv (μf v) (ff v) (ff' v) := by
  refine ⟨fun v => conv_mem_SB (hf.1 v) (hf'.1 v), ?_⟩
  filter_upwards [hf.2, hf'.2, h1] with v e e' e1
  rw [e, e', conv_unitLoc, Measure.real, e1]
  simp

theorem IsFinFamily.mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    IsFinFamily σ J L fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  refine ⟨fun v => ⟨(hf.1 v).1.mul ((hf'.1 v).1.comp_continuous (by fun_prop)), (hf.1 v).2.mul_right⟩, ?_⟩
  filter_upwards [hf.2, hf'.2, eventually_proj_mem_stabLoc σ J L y] with v e e' hy
  rw [e, e', unitLoc_mul_translate hy]

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem hecke_induction {p : (G → ℂ) → Prop} (h0 : p 0)
    (hadd : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, p f → p f' → p (f + f'))
    (hind : ∀ (r : ℂ) (g : G), p (r • dosetInd ℂ K g)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : p f := by
  classical
  obtain ⟨e, he⟩ := Final.HeckeBasis G K ℂ
  suffices ∀ a, p (e.symm a) by simpa using this (e ⟨f, hf⟩)
  intro a
  induction a using Finsupp.induction_linear with
  | zero => simpa using h0
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ (e.symm a).2 _ (e.symm b).2 ha hb
  | single c r =>
    obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk K K g = c := Quotient.exists_rep c
    convert hind r g
    funext x
    rw [← he, e.apply_symm_apply, Finsupp.single_apply, Pi.smul_apply, dosetInd, Set.indicator_apply]
    have : DoubleCoset.mk K K g = DoubleCoset.mk K K x ↔ x ∈ DoubleCoset.doubleCoset g (K : Set G) K := by
      rw [DoubleCoset.eq, DoubleCoset.mem_doubleCoset]; rfl
    by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]

theorem heckeVec_add (hK : IsCommensurated K) (ρ : Representation ℂ G V) {f f' : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (hf' : f' ∈ Hecke ℂ K) (x : V) : heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  simp only [heckeVec, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)

theorem heckeVec_smul (hK : IsCommensurated K) (ρ : Representation ℂ G V) (r : ℂ) {f : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (x : V) : heckeVec ρ K (r • f) x = r • heckeVec ρ K f x := by
  simp only [heckeVec, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (smul_finsum' r (finite_heckeVec hK hf ρ x)).symm

theorem dosetInd_comp (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') (t : H) :
    dosetInd ℂ K' t ∘ e = dosetInd ℂ K (e.symm t) := by
  funext g
  have : e g ∈ DoubleCoset.doubleCoset t (K' : Set H) K' ↔ g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨e.symm a, (hK _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), e.injective (by simpa using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨e a, (hK _).1 ha, e b, (hK _).1 hb, by simp⟩
  by_cases hg : g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K
  · simp [dosetInd, hg, this.2 hg]
  · simp [dosetInd, hg, mt this.1 hg]

theorem dosetInd_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) (t : G) : dosetInd ℂ K (a * t * b) = dosetInd ℂ K t := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, rfl⟩)]

end Generic

section Unitary

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  {σ : w.adicCompletion E →+* w.adicCompletion E} {n q : ℕ} {ϖ : w.adicCompletion E}
  {V : Type} [AddCommGroup V] [Module ℂ V]


open GlobalTheory.InertThetaCompare in
theorem cartanU (hU : IsUnramInv ϖ σ q) (g : GU σ n) : ∃ (d : Fin n → ℤ) (t : GU σ n), Antitone d ∧
    t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  have hϖ : IsUnifV E w ϖ := hU.2.2.2.1
  obtain ⟨d, hd, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp E w n ϖ (mem_Ov_of_isUnifV hϖ) hϖ g.1
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  have hh' : h ∈ GLint (Fin n) (Ov E w) := hh
  have hd' : ∀ i : Fin n, (List.ofFn d).getD i.1 0 = d i := fun i => by simp [List.getD_eq_getElem?_getD]
  have hG : Good n (List.ofFn d) := good_of_unitary hU (π := ϖ) hϖ (by simp)
    (List.pairwise_ofFn.2 fun i j hij => hd hij.le)
    (GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eh) g.2)
    ⟨h * k₁, mul_mem hh' h₁, k₂ * h⁻¹, mul_mem h₂ (inv_mem hh'), by
      simp only [Units.val_mul, e, hd', inv_inv, Matrix.mul_assoc]; rfl⟩
  obtain ⟨t, ht, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => ϖ ^ (List.ofFn d).getD i.1 0) fun i => by
    rw [map_zpow₀, hU.2.2.1, hG.rev, ← zpow_add₀ (unif_ne_zero hU), add_neg_cancel, zpow_zero]
  simp only [hd'] at ht
  exact ⟨d, t, hd, ht, dc_GU hU (a := k₁) (b := k₂) h₁ h₂ (Units.ext (by simp only [Units.val_mul, ht]; exact e))⟩

theorem isSatVecU_of_diag (hU : IsUnramInv ϖ σ q) {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (h0 : x ≠ 0) (hx : x ∈ fixed ρ (KU σ n))
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      heckeVec ρ (KU σ n) (dosetInd ℂ (KU σ n) t) x = SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) • x) :
    IsSatVecU ϖ q ρ x α := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hm := Final.DosetIndMem _ (KU σ n) ℂ
  refine ⟨h0, hx, fun f hf => ?_⟩
  refine hecke_induction (K := KU σ n)
    (p := fun f => heckeVec ρ (KU σ n) f x = SatU ϖ q f (fun i => (α i : ℂ)) • x) ?_ ?_ ?_ hf
  · simp [heckeVec, SatU]
  · intro f hf f' hf' h1 h2
    have := hy.2.2 _ (add_mem hf hf')
    rw [heckeVec_add hK _ hf hf', hy.2.2 _ hf, hy.2.2 _ hf', ← add_smul] at this
    rw [heckeVec_add hK _ hf hf', h1, h2, ← add_smul, smul_left_injective ℂ hy.1 this]
  · intro r g
    obtain ⟨d, t, hd, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
    rw [dosetInd_mul h₁ h₂]
    have := hy.2.2 _ (Submodule.smul_mem _ r (hm t))
    rw [heckeVec_smul hK _ r (hm t), hy.2.2 _ (hm t), smul_smul] at this
    rw [heckeVec_smul hK _ r (hm t), h d t hd ht, smul_smul, smul_left_injective ℂ hy.1 this]

end Unitary

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsEigenSys (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (c : List ℤ → ℂ) : Prop :=
  ∀ (a : GL (Fin n) (w.adicCompletion E)) (g : GLoc σ J v) (d : Fin n → ℤ) (u : Fin n → w.adicCompletion E),
    IsFrameAt w L a → Antitone d → (∀ i, Valued.v (u i) = WithZero.exp (-d i)) →
    (a⁻¹ * locMat σ J h g * a).1 = Matrix.diagonal u →
    heckeVec ρ (stabLoc σ J L v) (dosetInd ℂ (stabLoc σ J L v) g) x = c (List.ofFn d) • x

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {c : List ℤ → ℂ}
  {B : Multiset ℂˣ}

theorem IsEigenSys.split (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x =
      c (List.replicate j 1 ++ List.replicate (n - j) 0) • x := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let t : GL (Fin n) (w.adicCompletion E) := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (by
    rw [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0])
  have ht : Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (KGL w (n := n)) t := by
    rw [Tj, dosetInd]
    congr 1
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, Units.ext e⟩,
      fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, congrArg Units.val e⟩⟩
  obtain ⟨⟨a, ha, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Tj_mem_hecke hϖ j).1 hx, ht, dosetInd_comp e e2,
    hc a (e.symm t) (fun i => if i.1 < j then 1 else 0) (fun i => if i.1 < j then ϖ else 1) ha
      (fun i k hik => ?_) (fun i => ?_) (by rw [← e1, e.apply_symm_apply]; rfl)]
  · congr 2
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    by_cases hi : i < j <;> simp [hi, List.getElem_append]
  · have : i.1 ≤ k.1 := hik
    dsimp only
    split_ifs <;> omega
  · split_ifs
    · exact hϖ
    · simp

theorem IsEigenSys.inert (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {τ : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU τ n} (he : IsInertChart σ J L h τ e)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {d : Fin n → ℤ} {t : GU τ n} (hd : Antitone d)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KU τ n) (dosetInd ℂ (KU τ n) t) x = c (List.ofFn d) • x := by
  obtain ⟨-, ⟨a, ha, -, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Final.DosetIndMem _ _ ℂ t).1 hx, dosetInd_comp e e2,
    hc a (e.symm t) d _ ha hd (fun i => ?_) (by rw [← e1, e.apply_symm_apply, ht])]
  rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
  simp

theorem IsEigenSys.isSysParam (hc : IsEigenSys σ J L h ρ x c) (hB : IsParamVec σ J L h ρ x B) :
    IsSysParam σ n h c B := by
  have hx := hB.mem_fixed
  rcases hB with ⟨hv, e, he, hB⟩ | ⟨hw, τ, ϖ, e, α, hU, he, hB, rfl⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    exact Or.inl ⟨hv, hB.2.2.1, fun j hj =>
      smul_left_injective ℂ hB.1 ((hc.split hx he hϖ hj).symm.trans (hB.2.2.2 ϖ hϖ j hj))⟩
  · exact Or.inr ⟨hw, τ, ϖ, α, hU, he.1, rfl, fun d t hd ht => smul_left_injective ℂ hB.1
      ((hc.inert hx he hU.2.2.2.1 hd ht).symm.trans (hB.2.2 _ (Final.DosetIndMem _ _ ℂ t)))⟩

theorem IsEigenSys.isParamVec (hc : IsEigenSys σ J L h ρ x c) (h0 : x ≠ 0) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    (hs : IsSplit (E := E) v → ∃ e, IsSplitChart σ J L h e)
    (hi : IsInertAt F E v w → ∀ τ, IsConjAt σ h τ → ∃ e, IsInertChart σ J L h τ e)
    (hB : IsSysParam σ n h c B) : IsParamVec σ J L h ρ x B := by
  rcases hB with ⟨hv, h1, h2⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, h2⟩
  · obtain ⟨e, he⟩ := hs hv
    exact Or.inl ⟨hv, e, he, h0, (mem_fixed_comp_symm e he.2).2 hx, h1, fun ϖ hϖ j hj => by
      rw [hc.split hx he hϖ hj, h2 j hj]⟩
  · obtain ⟨e, he⟩ := hi hw τ hτ
    exact Or.inr ⟨hw, τ, ϖ, e, α, hU, he, isSatVecU_of_diag hU h0 ((mem_fixed_comp_symm e he.2.2).2 hx)
      fun d t hd ht => by rw [hc.inert hx he hU.2.2.2.1 hd ht, h2 d t hd ht], rfl⟩

end Place

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatMove

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_hatL {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hz ⊢
  intro i
  have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z) = (intGL F E n y).1 *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    change β⁻¹ * (β * intGL F E n y * β⁻¹) = _
    group
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hq : Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom q ∈ St β)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have h := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _
    (mulVec_mem_hatL hβ hq (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl


omit [NumberField F] [NumberField E] in
theorem bc_map_bc_inclR {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (g : GL (Fin n) E) :
    Formalism.UG.bc (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g) =
      Formalism.UG.bc (inclR (F := F) S) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.map f (AlgHom.id F E) (1 ⊗ₜ g.1 i j) = 1 ⊗ₜ g.1 i j
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl


omit [NumberField F] [NumberField E] in
theorem span_move {R O : Type} [CommRing R] [Algebra F R] [CommRing O] [Algebra O E] (H : AddSubgroup (Fin n → R ⊗[F] E))
    (g : GL (Fin n) E) (h q : GL (Fin n) (R ⊗[F] E)) (h1 : ∀ z ∈ H, q.1 *ᵥ z ∈ H) (h2 : ∀ z ∈ H, (q⁻¹).1 *ᵥ z ∈ H) :
    Submodule.span O {x : Fin n → E |
        ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H} =
      (Submodule.span O {x : Fin n → E | (h⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H}).map
        ((Matrix.mulVecLin g.1).restrictScalars O) := by
  have hv : ∀ (g : GL (Fin n) E) (x : Fin n → E),
      (Formalism.UG.bc (inclR (F := F) R) g).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) = fun i => (1 : R) ⊗ₜ[F] (g.1 *ᵥ x) i := by
    intro g x
    funext i
    exact (RingHom.map_mulVec (inclR (F := F) R) g.1 x i).symm
  have key : ∀ z, (q⁻¹).1 *ᵥ z ∈ H ↔ z ∈ H := by
    refine fun z => ⟨fun hz => ?_, h2 z⟩
    have := h1 _ hz
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
  have hs : ∀ x : Fin n → E,
      ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) =
        (q⁻¹).1 *ᵥ ((h⁻¹).1 *ᵥ fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ x) i) := by
    intro x
    rw [← hv, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      mul_inv_rev, mul_inv_rev, mul_assoc]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(g⁻¹).1 *ᵥ x, (key _).1 (hs x ▸ hx), ?_⟩
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    change _ *ᵥ _ ∈ H
    rw [hs, key]
    change _ *ᵥ (fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ (g.1 *ᵥ y)) i) ∈ H
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy

end General

variable {D : D7}

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧
    (Bridge.ratF V γ).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
  obtain ⟨γE, -, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  refine ⟨γE, hm, ?_⟩
  change finHom V γ.1 = _
  rw [finHom, MonoidHom.comp_apply, hm]
  exact bc_map_bc_inclR _ _

theorem hLat_eq_span {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (h : Bridge.Gf V) :
    Bridge.hLat V h = Submodule.span (𝓞 D.host.E) {x : Fin V.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))} := by
  rw [GlobalTheory.PrincInLevel.eq_latC hΛ, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  rfl

theorem mulVec_mem_hat_swap {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)} (hq : Formalism.UG.bc (swapAE D) q ∈ St β) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)),
      q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
  fun _ hz => mulVec_mem_hat hβ hq hz

theorem hLat_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (g h q : Bridge.Gf V) (γE : GL (Fin V.rank) D.host.E)
    (hf : g.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE) (hq : Formalism.UG.bc (swapAE D) q.1 ∈ St β) :
    Bridge.hLat V (g * h * q) = (Bridge.hLat V h).map ((Matrix.mulVecLin γE.1).restrictScalars (𝓞 D.host.E)) := by
  have hfr : IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hq' : Formalism.UG.bc (swapAE D) (q.1⁻¹) ∈ St β := by
    rw [MonoidHom.map_inv]; exact (St β).inv_mem hq
  have e : (g * h * q).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE * h.1 * q.1 := hf ▸ rfl
  rw [hLat_eq_span hΛ, hLat_eq_span hΛ, e]
  exact span_move _ γE h.1 q.1 (mulVec_mem_hat_swap hfr hq) (mulVec_mem_hat_swap hfr hq')

theorem hLat_rat_mul_stab : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ γ : GQ V, ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧ ∀ h q : Bridge.Gf V, Formalism.UG.bc (swapAE D) (q : GL (Fin V.rank) _) ∈ St β → Bridge.hLat V (Bridge.ratF V γ * h * q) = Formalism.HermitianLatticesTheory.gmap ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V h) := by
  intro D V β Λ hΛ γ
  obtain ⟨γE, hγ, hf⟩ := exists_ratMat V γ
  refine ⟨γE, hγ, fun h q hq => ?_⟩
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]
  exact hLat_mul hΛ _ h q γE hf hq

end GlobalTheory.HLatMove
end

