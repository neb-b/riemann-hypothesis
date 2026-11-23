module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixRealSizeLeConstMulOfCompactTranslate
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.RealMove

open GlobalTheory.Unf GlobalTheory.Unf.MajMeas

theorem realSize_mul_le_mul {D : D7} (θ : InfFam D) {m r n : ℕ} (Y : Mx D m r) (a : Mx D r n) :
    realSize θ (Y * a) ≤ n * realSize θ Y * realSize θ a := by
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = n * realSize θ Y * realSize θ a := by
        have h : ∀ τ i, ∑ _j : Fin n, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a =
            n * (∑ l, ‖compAt θ τ Y i l‖) * realSize θ a := by
          intro τ i
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, mul_assoc]
        simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum]
        rfl

theorem realSize_le_of_isCompact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.realSize θ x ≤ C * GlobalTheory.Unf.realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := by
  intro D θ hθ V n Q hQ
  have hc : Continuous (fun y : GA D V => realSize θ (Formalism.L2.Theta.mt V y)) :=
    (continuous_realSize hθ).comp (GlobalTheory.Core.Rk.Level.continuous_mt' V)
  obtain ⟨M, hM⟩ := (hQ.image hc).bddAbove
  refine ⟨max 1 (n * M), le_max_left _ _, fun y hy x => ?_⟩
  set a : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with ha
  have e : x = (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by
    rw [ha]
    rw [← Matrix.mul_assoc, ← GlobalTheory.Core.Rk.Level.mt_mul', mul_inv_cancel, GlobalTheory.Core.Rk.Level.mt_one',
      Matrix.one_mul]
  have hyM : realSize θ (Formalism.L2.Theta.mt V y) ≤ M := hM ⟨y, hy, rfl⟩
  have h0 := realSize_nonneg θ a
  have h1 := realSize_nonneg θ (Formalism.L2.Theta.mt V y)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc realSize θ x = realSize θ (HMul.hMul (Formalism.L2.Theta.mt V y) a : Mx D V.rank n) := by rw [← e]
    _ ≤ n * realSize θ (Formalism.L2.Theta.mt V y) * realSize θ a :=
        realSize_mul_le_mul θ _ _
    _ ≤ (n * M) * realSize θ a := by gcongr
    _ ≤ max 1 (n * M) * realSize θ a := by gcongr; exact le_max_right _ _

end GlobalTheory.Unf.RealMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfPoint
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.HSElim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_eq_zero_of_point {F K : Type} [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
    {N e δ : ℕ} {P : Ideal (MvPolynomial (Fin N) F)} {f : MvPolynomial (Fin (e + 1) × Fin N) F}
    (hf : IsChowFormInt P e δ f) (s : Fin (e + 1) → Fin N → K) (y : Fin N → K) (hy : y ≠ 0)
    (hyP : ∀ a ∈ P, aeval y a = 0) (hs : ∀ i, ∑ j, s i j * y j = 0) :
    aeval (fun p : Fin (e + 1) × Fin N => s p.1 p.2) f = 0 := by
  let φ : K ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F K (AlgebraicClosure F)
  have hmap : ∀ {σ : Type} (x : σ → K) (a : MvPolynomial σ F),
      aeval (fun i => φ (x i)) a = φ (aeval x a) := fun x a =>
    (AlgHom.congr_fun (MvPolynomial.comp_aeval (f := x) (φ : K →ₐ[F] AlgebraicClosure F)) a).symm
  have key : aeval (fun p : Fin (e + 1) × Fin N => φ (s p.1 p.2)) f = 0 := by
    refine (hf.zero_iff _).2 ⟨fun j => φ (y j), ?_, fun a ha => ?_, fun i => ?_⟩
    · intro h
      apply hy
      funext j
      have := congrFun h j
      simpa using this
    · rw [hmap, hyP a ha, map_zero]
    · have := congrArg φ (hs i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_mul] using this
  rw [hmap (fun p : Fin (e + 1) × Fin N => s p.1 p.2)] at key
  simpa using key

theorem exists_elim_form : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ)
    (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime →
    (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) →
    ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I →
    ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ D * d * hilbertDegree I ∧
      ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin D → Fin N → K)
        (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 →
        (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hp hcomp hdim hg hgI
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have hIh := GlobalTheory.ChowExists.isHomogeneous_of_component hcomp
  obtain ⟨f0, hf0⟩ := GlobalTheory.ChowExists.exists_isChowFormInt hp hIh hdim
  obtain ⟨i0, hi0⟩ := GlobalTheory.ChowExists.exists_X_notMem hf0
  have hJh := isHomogeneous_sup_span_singleton hIh hg
  have hex : ∀ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset,
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) F, IsChowFormInt P e (hilbertDegree P) f := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    have hPp := hP.1.1.1
    obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup hIh hdim hg hgI hP
    obtain rfl : e = e' := by omega
    exact GlobalTheory.ChowExists.exists_isChowFormInt hPp (isHomogeneous_of_mem_projComponents hJh hP) h2
  choose! f hf using hex
  refine ⟨∏ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, f P, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun P hP => (hf P hP).ne_zero
  · refine (totalDegree_finsetProd _ _).trans ?_
    have h1 : ∑ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, (f P).totalDegree =
        (e + 1) * projSetDegree (I ⊔ Ideal.span {g}) := by
      rw [projSetDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P hP => GlobalTheory.ChowSection.totalDegree_of_isChowFormInt (hf P hP)
    rw [h1, mul_assoc]
    exact Nat.mul_le_mul_left _ (projSetDegree_sup_le_of_isPrime hIh hi0 hg hgI)
  · intro K _ _ _ s y hy hyI hyg hs
    rw [map_prod]
    let Jy : Ideal (MvPolynomial (Fin N) F) := RingHom.ker (aeval y : MvPolynomial (Fin N) F →ₐ[F] K)
    have hJy : I ⊔ Ideal.span {g} ≤ Jy := sup_le (fun a ha => (RingHom.mem_ker).2 (hyI a ha))
      ((Ideal.span_singleton_le_iff_mem _).2 ((RingHom.mem_ker).2 hyg))
    have : Jy.IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hPc : P ∈ projComponents (I ⊔ Ideal.span {g}) :=
      ⟨hPmin, i, fun h => hi (by simpa using (RingHom.mem_ker).1 (hPle h))⟩
    have hPf : P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset :=
      (Set.Finite.mem_toFinset _).2 hPc
    exact Finset.prod_eq_zero hPf (aeval_eq_zero_of_point (hf P hPf) s y hy
      (fun a ha => (RingHom.mem_ker).1 (hPle ha)) hs)

end GlobalTheory.HSElim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGenerated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hmono : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist G M') 0 ≤ hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G (isLB_lbPow hL.isLB m) hM' h
      exact (hdim_congr k 0 e).ge
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h2 := ih _ (isLB_tens hM' hB.isLB) (by rw [h1, h, succ_nsmul']; abel)
      exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp G B _ M' hB.isLB _ hM' t ht h1).2.2).trans h2
  have hch : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + j * hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB m) hM' h
      rw [hdim_congr k 0 e]
      omega
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h0 : cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls (tens M' B) (isLB_tens hM' hB.isLB) + j • cls B hB.isLB := by
        rw [h1, h, succ_nsmul']; abel
      have h2 := ih _ (isLB_tens hM' hB.isLB) h0
      have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp (GlobalTheory.structureModule X) B _ M' hB.isLB _ hM' s hs h1).1 0
      change hdim k (twist (GlobalTheory.structureModule X) (tens M' B)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + hdim k (twist G (tens M' B)) 0 at h3
      have h4 := hmono j _ (isLB_tens hM' hB.isLB) h0
      rw [Nat.succ_mul]
      omega
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch m (lbPow M m) (isLB_lbPow hM m) hcl
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPos
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.AmplePos

theorem pos_of_bound {h : ℕ → ℕ} {d C m₀ : ℕ} {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hf : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ h m)
    (hb : ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ d| ≤
      C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) : 0 < a := by
  by_contra ha
  rw [not_lt] at ha
  obtain ⟨m, hm1, hm2⟩ := (hf.and_eventually (eventually_ge_atTop
    (max m₀ (max 1 (⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1))))).exists
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm2
  have hm1' : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hmK' : ⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  have hmK : (C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c) < m := by
    have h1 := Nat.le_ceil ((C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c))
    have h2 : ((⌈(C : ℝ) * d * 2 ^ (d - 1) / ((d.factorial : ℝ) * c)⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hmK'
    push_cast at h2
    linarith
  have hint : (d.factorial : ℤ) * (h m : ℤ) ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
    have h3 := (abs_le.mp (hb m hmm₀)).2
    have h4 : a * (m : ℤ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (by positivity)
    linarith
  have hreal : (d.factorial : ℝ) * (h m : ℝ) ≤ (C : ℝ) * ((d : ℝ) * ((m : ℝ) + 1) ^ (d - 1)) := by
    have h5 := (Int.cast_le (R := ℝ)).mpr hint
    push_cast at h5
    exact h5
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one] at hreal hm1
    linarith
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hreal hmK
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1'
    have h5 : ((m : ℝ) + 1) ^ e ≤ 2 ^ e * (m : ℝ) ^ e := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) e
    have hFc : 0 < (((e + 1).factorial : ℕ) : ℝ) * c := mul_pos hF hc
    rw [div_lt_iff₀ hFc] at hmK
    have h6 : (((e + 1).factorial : ℕ) : ℝ) * (c * (m : ℝ) ^ (e + 1)) ≤
        (((e + 1).factorial : ℕ) : ℝ) * (h m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hF.le
    have hCpos : (0 : ℝ) ≤ C := by positivity
    have h7 : (C : ℝ) * (((e + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ e) ≤
        (C : ℝ) * (((e + 1 : ℕ) : ℝ) * (2 ^ e * (m : ℝ) ^ e)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hme : (0 : ℝ) < (m : ℝ) ^ e := by positivity
    have h8 := mul_lt_mul_of_pos_right hmK hme
    have h9 : (m : ℝ) ^ (e + 1) = m * m ^ e := by ring
    rw [h9] at h6
    nlinarith [h6, hreal, h7, h8]

theorem topSelf_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) →
    ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  intro k _ _ X _ _ hp d hd A hA
  obtain ⟨D, hD, c, hc, hf⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDd : D = d := by
    rw [hD] at hd
    exact_mod_cast hd
  subst hDd
  have hsupp : suppDim (structureModule X) ≤ (D : ℕ) := by
    unfold GlobalTheory.QCoh.suppDim
    rw [← hD]
    exact topologicalKrullDim_subspace_le _ _
  obtain ⟨C, m₀, hb⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp D (structureModule X) hsupp A hA
  rw [topSelf_def]
  exact pos_of_bound hc hf hb

end GlobalTheory.AmplePos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := g.1.1

def latD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | z ∘ Sum.inl ∈ GlobalTheory.InertSph.latAt W v ∧ z ∘ Sum.inr ∈ GlobalTheory.InertSph.latAt W v}

def KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧ ∀ z ∈ latD W v, matD g *ᵥ z ∈ latD W v ∧ matD g⁻¹ *ᵥ z ∈ latD W v}

def PDiag (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def PAnti (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * antiCols d = antiCols d * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

end GlobalTheory.DblVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutatorStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archHeisenbergDerivative_additive_commutator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  first | exact @GlobalTheory.HeisDerivLaws.heis_deriv_laws | exact GlobalTheory.HeisDerivLaws.heis_deriv_laws | (intros; apply GlobalTheory.HeisDerivLaws.heis_deriv_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZero
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.L2InnerProductNonvanishing

theorem integral_mul_star_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (f : SInf F κ) (hf : f ≠ 0) :
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI hH : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : FiniteDimensional ℝ (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth :=
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hL2 : MeasureTheory.MemLp (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) 2 MeasureTheory.volume := f.memLp 2 MeasureTheory.volume
  have hint : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := hL2.integrable_norm_pow (by norm_num)
  have h1 : ∀ x, f x * star (f x) = (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    intro x
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  simp_rw [h1]
  rw [integral_complex_ofReal]
  rw [Complex.ofReal_ne_zero]
  apply ne_of_gt
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  have hopen : IsOpen (Function.support fun x => ‖f x‖ ^ 2) := by
    exact (continuous_norm.comp f.continuous).pow 2 |>.isOpen_support
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  exact IsOpen.measure_pos (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) hopen
    ⟨x, by simpa using hx⟩

end GlobalTheory.L2InnerProductNonvanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebraStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CasCentre.cas_Eop_mem_Zalg | exact GlobalTheory.CasCentre.cas_Eop_mem_Zalg | (intros; apply GlobalTheory.CasCentre.cas_Eop_mem_Zalg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_coordinate_ratio_bounded : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  first | exact @GlobalTheory.cone_ratio_bounded | exact GlobalTheory.cone_ratio_bounded | (intros; apply GlobalTheory.cone_ratio_bounded <;> assumption)
end

