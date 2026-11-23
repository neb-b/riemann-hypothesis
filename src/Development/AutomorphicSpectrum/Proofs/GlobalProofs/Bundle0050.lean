module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermModerateGrowthInherited
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

section General

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.UAut.ConstAut
open GlobalTheory.ThK.SmoothLev (IsSmModOn)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSmModOn_constTermOn (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {C : Matrix (Fin n) (Fin r) E}
    (d : Fin r → ℕ) (hC : IsIsoCols σ J C) {Γ : Set (GAd σ J)} {φ c : GAd σ J → ℂ}
    (hΓ : ((ratPts σ J ⊓ parFlag σ J C d : Subgroup (GAd σ J)) : Set (GAd σ J)) ⊆ Γ)
    (hφ : IsSmModOn σ J Γ φ) (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c) :
    IsSmModOn σ J (leftGrp σ J C d : Set (GAd σ J)) c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hs : IsSm σ J φ := hφ.smooth
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hΓ hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    _root_.GlobalTheory.DerCont.continuous_foldr_lineDer F E σ h n J hJ φ hφ.level hφ.cont hs
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hs hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hsm : IsSm σ J c := by
    obtain ⟨dd, δ, hδ, hW⟩ := _root_.GlobalTheory.UnitChart.exists_realLines_chart F E σ h n J hJ
    intro k γ hγ g
    have := _root_.GlobalTheory.Cusp.contDiff_constTermOn_param hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
      (fun γ' hγ' x t => by simp only [mul_assoc]; exact hφΓ γ' hγ' _) (fun x => hs k γ hγ x)
      (_root_.GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine F E σ h n J hJ dd δ hδ hW φ hφ.level hs k γ hγ) g
    simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs'⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs' x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, hsm, hgrowth⟩, hct⟩

theorem depth_lt {r t : ℕ} (ht : t ≤ r) {T : Finset (Fin r)} {i j : Fin t} {k : Fin r} (hk : k ∈ T)
    (h1 : j.val ≤ k.val) (h2 : k.val < i.val) :
    (T.filter (· < Fin.castLE ht j)).card < (T.filter (· < Fin.castLE ht i)).card := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Fin.lt_def, Fin.val_castLE] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · have h3 := hsub (Finset.mem_filter.2 ⟨hk, Fin.lt_def.2 (by simpa using h2)⟩)
    have h4 := Fin.lt_def.1 (Finset.mem_filter.1 h3).2
    simp only [Fin.val_castLE] at h4
    omega

theorem exists_block_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin t) (Fin t) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card)
    (e : M * adMat F (X.submatrix id (Fin.castLE ht)) = adMat F (X.submatrix id (Fin.castLE ht)) * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hst) (Fin.castLE hst), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (depth_lt ht (hST hk1.1) (i := Fin.castLE hst i) (j := Fin.castLE hst j) (by simpa using h1) (by simpa using h2))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hst j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F (X.submatrix id (Fin.castLE ht))) x (Fin.castLE hst j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hst) (Fin.castLE_injective hst) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    obtain ⟨k, hk, hjk⟩ := (hS (Fin.castLE hs j)).1 (by simp)
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    have hz : B i (Fin.castLE hst j) = 0 :=
      hB (depth_lt ht (hST hk) (by simpa [Fin.le_def] using hjk) (by omega))
    rw [hz, mul_zero]

theorem parFlag_le_of_subset {r s t : ℕ} (X : Matrix (Fin n) (Fin r) E) {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hs : s ≤ r) (ht : t ≤ r) (hst : s ≤ t) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) :
    parFlag σ J (X.submatrix id (Fin.castLE ht)) (fun i : Fin t => (T.filter (· < Fin.castLE ht i)).card) ≤
      parFlag σ J (X.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) :=
  fun _ ⟨⟨B, hB, e⟩, B', hB', e'⟩ =>
    ⟨exists_block_of_subset X hST hs ht hst hS hB e, exists_block_of_subset X hST hs ht hst hS hB' e'⟩

def top {r : ℕ} (S : Finset (Fin r)) : ℕ := S.sup fun k => k.val + 1

theorem top_le {r : ℕ} (S : Finset (Fin r)) : top S ≤ r := Finset.sup_le fun k _ => k.2

theorem top_mono {r : ℕ} {S T : Finset (Fin r)} (h : S ⊆ T) : top S ≤ top T := Finset.sup_mono h

theorem lt_top_iff {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : i.val < top S ↔ ∃ k ∈ S, i ≤ k := by
  rw [top, Finset.lt_sup_iff]
  exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega

theorem leftGrp_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) :
    leftGrp σ J (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) =
      GlobalTheory.StdPar.unip σ J X S ⊔ (ratPts σ J ⊓ GlobalTheory.StdPar.levi σ J X Y S) := by
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (top S) (top_le S) (lt_top_iff S)
    (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) fun _ => rfl
  have hg := (_root_.GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ (top S) (X.submatrix id (Fin.castLE (top_le S)))
    (Y.submatrix id (Fin.castLE (top_le S))) (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective _))).2.2.1
  rw [hg, hu, hl]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

theorem isSmModOn_constAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T → T.Nonempty → ∀ φ c : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ → IsConstAlong D.sp.cm.sig V.gram X T φ c → IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) c ∧ ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c) := by
  intro D V m X Y hW S T hST _ φ c hφ hc
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  obtain ⟨hu, -, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig h _ V.gram hJ m X Y hW T (top T) (top_le T) (lt_top_iff T)
    (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) fun _ => rfl
  have hC := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (GlobalTheory.SiegelSet.sigma_sigma h) hJ (top_le T)
  have hc' : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.UAut.unipFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card)) φ c := hu ▸ hc
  have hΓ : ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram ⊓ GlobalTheory.UAut.parFlag D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
      (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) : Subgroup (GA D V)) : Set (GA D V)) ⊆
      (leftSub V X Y S : Set (GA D V)) := by
    intro p hp
    have e := leftGrp_eq h hJ hW S
    have : p ∈ GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le S)))
        (fun i : Fin (top S) => (S.filter (· < Fin.castLE (top_le S) i)).card) :=
      Subgroup.mem_sup_right ⟨hp.1, parFlag_le_of_subset X hST (top_le S) (top_le T) (top_mono hST) (lt_top_iff S) hp.2⟩
    rw [e] at this
    exact this
  obtain ⟨r1, r2⟩ := isSmModOn_constTermOn h hJ _ hC hΓ hφ hc'
  refine ⟨?_, fun l hl => ?_⟩
  · have e : (leftSub V X Y T : Subgroup (GA D V)) = GlobalTheory.UAut.leftGrp D.sp.cm.sig V.gram (X.submatrix id (Fin.castLE (top_le T)))
        (fun i : Fin (top T) => (T.filter (· < Fin.castLE (top_le T) i)).card) := (leftGrp_eq h hJ hW T).symm
    rw [e]
    exact r1
  · have := r2 l hl
    rw [← hu] at this
    exact this

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstMod

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermSmoothModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

open MeasureTheory GlobalTheory.SiegelSet GlobalTheory.Mem.AutSpace GlobalTheory.SphSmooth

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def pairSpan (V : HSp D) (φ c : GA D V → ℂ) : Submodule ℂ ((GA D V → ℂ) × (GA D V → ℂ)) :=
  Submodule.span ℂ {p | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧
    p = (l.foldr lineDer φ, l.foldr lineDer c)}

theorem pairSpan_le (φ c : GA D V → ℂ) : pairSpan V φ c ≤ (derSpan V φ).prod (derSpan V c) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩

theorem Rder_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (Rder θ V τ X p.1, Rder θ V τ X p.2) ∈ pairSpan V φ c := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨oneP θ V τ X :: l, List.forall_mem_cons.2 ⟨isRealLine_oneP hθ V hX, hl⟩, rfl⟩
  | zero =>
    have := Rder_smul (θ := θ) 0 (0 : GA D V → ℂ) τ X
    rw [zero_smul, zero_smul] at this
    simp only [Prod.fst_zero, Prod.snd_zero, this]
    exact zero_mem (pairSpan V φ c)
  | add x y hx hy ihx ihy =>
    have h1 := pairSpan_le φ c hx
    have h2 := pairSpan_le φ c hy
    simp only [Prod.fst_add, Prod.snd_add]
    rw [Rder_add (derSpan_le hθ hφ h1.1) (derSpan_le hθ hφ h2.1) hX,
      Rder_add (derSpan_le hθ hc h1.2) (derSpan_le hθ hc h2.2) hX]
    exact add_mem ihx ihy
  | smul a x _ ih =>
    simp only [Prod.smul_fst, Prod.smul_snd, Rder_smul]
    exact Submodule.smul_mem _ a ih

theorem RderC_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) {p : (GA D V → ℂ) × (GA D V → ℂ)}
    (hp : p ∈ pairSpan V φ c) : (RderC θ V τ Z p.1, RderC θ V τ Z p.2) ∈ pairSpan V φ c := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  exact add_mem (Rder_mem_pairSpan hθ hφ hc h1 hp)
    (Submodule.smul_mem _ Complex.I (Rder_mem_pairSpan hθ hφ hc h2 hp))

theorem word_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (L : List ((GA D V → ℂ) → GA D V → ℂ)) (hL : ∀ A ∈ L, ∃ Z, A = RderC θ V τ Z) :
    (L.foldr (fun f acc => f acc) φ, L.foldr (fun f acc => f acc) c) ∈ pairSpan V φ c := by
  induction L with
  | nil => exact Submodule.subset_span ⟨[], by simp, rfl⟩
  | cons A L ih =>
    obtain ⟨Z, rfl⟩ := hL A List.mem_cons_self
    exact RderC_mem_pairSpan hθ hφ hc τ Z (ih fun B hB => hL B (List.mem_cons_of_mem _ hB))

theorem gelf_mem_pairSpan (hθ : IsInfFam θ) {φ c : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hc : c ∈ SmFun θ V) (τ : D.what₂.Tau)
    (k : ℕ) : (gelf θ V τ k φ, gelf θ V τ k c) ∈ pairSpan V φ c := by
  have e : (gelf θ V τ k φ, gelf θ V τ k c) = ∑ idx : Fin (k + 1) → Fin V.rank,
      ((List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) φ,
        (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) c) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; rfl
    · rw [Prod.snd_sum]; rfl
  rw [e]
  refine Submodule.sum_mem _ fun idx _ => word_mem_pairSpan hθ hφ hc τ _ fun A hA => ?_
  obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hA
  exact ⟨_, rfl⟩

variable {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

theorem good_of_mem_pairSpan (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) {φ c : GA D V → ℂ}
    (hφ : IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ)
    (h : ∀ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) →
      IsConstAlong D.sp.cm.sig V.gram X T (l.foldr lineDer φ) (l.foldr lineDer c))
    (μ : Measure (unip D.sp.cm.sig V.gram X T)) (𝓕 : Set (unip D.sp.cm.sig V.gram X T)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((GlobalTheory.AdelicU.ratPts D.sp.cm.sig V.gram).subgroupOf (unip D.sp.cm.sig V.gram X T)) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (g : GA D V) {p : (GA D V → ℂ) × (GA D V → ℂ)} (hp : p ∈ pairSpan V φ c) :
    IntegrableOn (fun u : unip D.sp.cm.sig V.gram X T => p.1 ((u : GA D V) * g)) 𝓕 μ ∧
      p.2 g = ∫ u in 𝓕, p.1 ((u : GA D V) * g) ∂μ := by
  have hJ : IsHermND D.sp.cm.sig V.gram :=
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨?_, h l hl μ 𝓕 hμ h𝓕 h1 g⟩
    obtain ⟨C, hC, hcov⟩ := _root_.GlobalTheory.CuspCocpt.cocompact_unip _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ _ X Y hW T
    have hcont := _root_.GlobalTheory.DerCont.continuous_foldr_lineDer _ _ _ (GlobalTheory.AdelicU.isCMExt_host D) _ _ hJ φ hφ.level hφ.cont hφ.smooth l hl
    have hleft := GlobalTheory.UAut.ConstAut.leftInv_foldr
      (Γ := (GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V))) (φ := φ) (fun γ hγ x => hφ.left γ hγ x) l
    refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _
      (hcont.comp (continuous_subtype_val.mul continuous_const)) fun γ hγ u => ?_
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hleft γ ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩ _
  | zero => exact ⟨integrableOn_zero, by simp⟩
  | add x y _ _ ihx ihy =>
    refine ⟨ihx.1.add ihy.1, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [ihx.2, ihy.2]
    exact (integral_add ihx.1 ihy.1).symm
  | smul a x _ ih =>
    refine ⟨ih.1.const_mul a, ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [ih.2]
    exact (integral_const_mul a _).symm

theorem isConstAlong_gelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (φ c : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram ((GQ V ⊓ unip D.sp.cm.sig V.gram X T : Subgroup (GA D V)) : Set (GA D V)) φ → GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram c → (∀ l : List (ℝ → GA D V), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram γ) → IsConstAlong D.sp.cm.sig V.gram X T (l.foldr GlobalTheory.SiegelSet.lineDer φ) (l.foldr GlobalTheory.SiegelSet.lineDer c)) → ∀ (τ : D.what₂.Tau) (k : ℕ), IsConstAlong D.sp.cm.sig V.gram X T (gelf θ V τ k φ) (gelf θ V τ k c) := by
  intro D θ hθ V m X Y hW T φ c hφ hc h τ k μ 𝓕 hμ h𝓕 h1 g
  have sφ : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram φ := hφ.smooth
  exact (good_of_mem_pairSpan hW T hφ h μ 𝓕 hμ h𝓕 h1 g
    (gelf_mem_pairSpan hθ (mem_smFun_of_isSm hθ sφ) (mem_smFun_of_isSm hθ hc) τ k)).2

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstGelf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def ptStab (A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)) : Subgroup (GAd σ J) where
  carrier := {g | ∀ y ∈ A, (matHom _ σ J g).1 *ᵥ y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

def block (T : Finset (Fin r)) (k : Fin r) : Set (Fin r) := {i | i ≤ k ∧ ∀ t ∈ T, t < k → t < i}

def upTo (T : Finset (Fin r)) : Set (Fin r) := {i | ∃ k ∈ T, i ≤ k}

variable (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r))

def glPart (k : Fin r) : Subgroup (GAd σ J) :=
  levi σ J X Y T ⊓ ptStab σ J (colPerp σ J X (block T k) ⊓ colPerp σ J Y (block T k))

def uPart : Subgroup (GAd σ J) := ptStab σ J (colSpan F X (upTo T) ⊔ colSpan F Y (upTo T))

def part : Option {k // k ∈ T} → Subgroup (GAd σ J)
  | none => uPart σ J X Y T
  | some k => glPart σ J X Y T k.1

end Groups

def sliceSet {G : Type} [Group G] (𝓒 : Set (G → ℂ)) (H L : Subgroup G) (b : G) : Set (H → ℂ) :=
  {f | ∃ φ ∈ 𝓒, ∃ y ∈ L, (∀ t ∈ H, t * y = y * t) ∧ f = fun t : H => φ ((t : G) * y * b)}


open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin in
def cuspOn {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}

section Slices

theorem exists_finset_sep {X : Type} (A : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset X, ∀ f ∈ A, (∀ x ∈ S, f x = 0) → f = 0 := by
  classical
  let ev : X → Module.Dual ℂ A := fun x => (LinearMap.proj x).comp A.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 (by rwa [Set.image_univ] : (s : Set (Module.Dual ℂ A)) ⊆ ev '' Set.univ)
  refine ⟨s', fun f hf h0 => ?_⟩
  have h1 : ∀ l ∈ Submodule.span ℂ ((s'.image ev : Finset _) : Set (Module.Dual ℂ A)), l ⟨f, hf⟩ = 0 := fun l hl => by
    induction hl using Submodule.span_induction with
    | mem l h =>
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact h0 x hx
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hb]
  funext x
  exact h1 (ev x) (e ▸ Submodule.subset_span ⟨x, rfl⟩)

theorem finiteDimensional_of_slices {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule ℂ (X i → ℂ))
    [∀ i, FiniteDimensional ℂ (A i)] (𝓕 : Set ((∀ i, X i) → ℂ))
    (h : ∀ f ∈ 𝓕, ∀ i x, (fun t => f (Function.update x i t)) ∈ A i) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓕) := by
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun t => f (Function.update x i t)) ∈ A i}
      add_mem' := fun {a b} ha hb i x => (A i).add_mem (ha i x) (hb i x)
      zero_mem' := fun i _ => (A i).zero_mem
      smul_mem' := fun a f hf i x => (A i).smul_mem a (hf i x) }
  choose S hS using fun i => exists_finset_sep (A i)
  let ev : P →ₗ[ℂ] ((∀ i, S i) → ℂ) :=
    { toFun := fun f s => f.1 fun i => (s i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ f : P, ev f = 0 → ∀ I : Finset ι, ∀ x : ∀ i, X i, (∀ i, i ∉ I → x i ∈ S i) → f.1 x = 0 := by
    intro f hf I
    induction I using Finset.induction_on with
    | empty =>
      intro x hx
      exact congrFun hf fun i => ⟨x i, hx i (by simp)⟩
    | insert a I _ ih =>
      intro x hx
      have := hS a _ (f.2 a x) fun t ht => ih _ fun i hi => by
        by_cases e : i = a
        · subst e; simpa using ht
        · rw [Function.update_of_ne e]
          exact hx i (by simp [e, hi])
      simpa using congrFun this (x a)
  have hinj : Function.Injective ev := (injective_iff_map_eq_zero ev).2 fun f hf =>
    Subtype.ext (funext fun x => key f hf Finset.univ x (by simp))
  haveI : FiniteDimensional ℂ P := FiniteDimensional.of_injective ev hinj
  exact Submodule.finiteDimensional_of_le (S₂ := P) (Submodule.span_le.2 fun f hf i x => h f hf i x)

end Slices

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
end
end

