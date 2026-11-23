module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Formalism.ConjugateSelfDual.StatementRest
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleInvariantPeriodMatrixBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.Per.PerMat

theorem li_of_frac {B : Type} [CommRing B] [IsDomain B] {d : ℕ} {ι G F : Type} [Fintype ι] [Field F]
    (κ : F →+* B) (σ : G → B →+* B) (M : G → Matrix (Fin d) (Fin d) B) (v : ι → Fin d → B)
    (hv : ∀ i g, (M g).mulVec (fun r => σ g (v i r)) = v i)
    (hfrac : ∀ a b : B, b ≠ 0 → (∀ g, σ g a * b = a * σ g b) → ∃ k : F, a = κ k * b)
    (hind : ∀ k : ι → F, ∑ i, κ (k i) • v i = 0 → k = 0) :
    LinearIndependent B v := by
  classical
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ n : ℕ, ∀ c : ι → B, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n →
      ∑ i, c i • v i = 0 → c = 0 by
    intro c hc i; exact congrFun (H _ c le_rfl hc) i
  intro n
  induction n with
  | zero =>
    intro c hcard _
    funext i
    by_contra h
    simp only [Pi.zero_apply] at h
    have hi : i ∈ Finset.univ.filter (fun i => c i ≠ 0) := by simp [h]
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard] at hi
  | succ n ih =>
    intro c hcard hc
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hσ : ∀ g, ∑ i, σ g (c i) • v i = 0 := by
      intro g
      have e1 : (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • (fun r => σ g (v i r)) := by
        funext r; simp [Finset.sum_apply, map_sum, map_mul]
      have h1 : (M g).mulVec (fun r => σ g ((∑ i, c i • v i) r)) = ∑ i, σ g (c i) • v i := by
        rw [e1, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_smul, hv]
      rw [← h1, hc]
      simp only [Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero (M g)
    have hrel : ∀ g i, σ g (c i) * c i0 = c i * σ g (c i0) := by
      intro g
      have key := ih (fun i => c i0 * σ g (c i) - σ g (c i0) * c i) ?_ ?_
      · intro i
        have := congrFun key i
        simp only [Pi.zero_apply] at this
        linear_combination this
      · have hsub : Finset.univ.filter (fun i => c i0 * σ g (c i) - σ g (c i0) * c i ≠ 0) ⊆
            (Finset.univ.filter (fun i => c i ≠ 0)).erase i0 := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
          refine ⟨?_, ?_⟩
          · rintro rfl; apply hi; ring
          · intro h0; apply hi; rw [h0]; simp
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simp [hi0])] at h2
        omega
      · have e : ∑ i, (c i0 * σ g (c i) - σ g (c i0) * c i) • v i =
            c i0 • ∑ i, σ g (c i) • v i - σ g (c i0) • ∑ i, c i • v i := by
          simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
        rw [e, hσ g, hc, smul_zero, smul_zero, sub_zero]
    choose k hk using fun i => hfrac (c i) (c i0) hi0 (fun g => hrel g i)
    have hk0 : ∑ i, κ (k i) • v i = 0 := by
      have h3 : c i0 • ∑ i, κ (k i) • v i = 0 := by
        calc c i0 • ∑ i, κ (k i) • v i = ∑ i, c i • v i := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_smul, hk i, mul_comm]
          _ = 0 := hc
      exact (smul_eq_zero.1 h3).resolve_left hi0
    have h4 := congrFun (hind k hk0) i0
    have h1 := hk i0
    rw [h4, Pi.zero_apply, map_zero, zero_mul] at h1
    exact hi0 h1

end GlobalTheory.Per.PerMat

namespace GlobalTheory.Per.PerMat

theorem exists_invertible_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i) → ∃ U U' : Matrix (Fin d) (Fin d) (Per.Bcris l), U * U' = 1 ∧ (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) := by
  intro l _ K P AI T d ρ hspan
  classical
  obtain ⟨-, hdom, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsDomain (Per.Bcris l) :=
    Function.Injective.isDomain (T.eB.symm : Per.Bcris l →+* P.R.B) T.eB.symm.injective
  choose m c v hv hsum using hspan
  let κ : ↥(K0 K) →+* Per.Bcris l := T.eB.toRingHom.comp (algebraMap ↥(K0 K) P.R.B)
  letI : Algebra ↥(K0 K) (Per.Bcris l) := κ.toAlgebra
  let S : Set (Fin d → Per.Bcris l) := Set.range (fun q : (Σ j, Fin (m j)) => v q.1 q.2)
  obtain ⟨b, hbS, hspanb, hli⟩ := exists_linearIndependent (↥(K0 K)) S
  have hfin : b.Finite := (Set.finite_range _).subset hbS
  haveI : Fintype b := hfin.fintype
  have hvb : ∀ (x : b) (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) ((x : Fin d → Per.Bcris l) r)) = x := by
    rintro ⟨x, hx⟩ g
    obtain ⟨⟨j, i⟩, rfl⟩ := hbS hx
    exact hv j i g
  have hliB : LinearIndependent (Per.Bcris l) (Subtype.val : b → Fin d → Per.Bcris l) := by
    refine li_of_frac κ (fun g : ↥(GK K) => Per.σB (g : GQ l)) (fun g => (ρ g).map (Per.zB l)) _ hvb ?_ ?_
    · intro a a' ha' h
      obtain ⟨k, hk⟩ := GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K (T.eB.symm a) (T.eB.symm a')
        (by simpa using ha') (fun g hg => by
          apply T.eB.injective
          rw [map_mul, map_mul, T.actB, T.actB]
          simpa using h ⟨g, hg⟩)
      refine ⟨k, ?_⟩
      have := congrArg T.eB hk
      simpa [κ] using this
    · intro k hk
      rw [Fintype.linearIndependent_iff] at hli
      funext x
      refine hli k ?_ x
      rw [← hk]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← algebraMap_smul (Per.Bcris l) (k y) (y : Fin d → Per.Bcris l)]
      rfl
  have hsp : ⊤ ≤ Submodule.span (Per.Bcris l) (Set.range (Subtype.val : b → Fin d → Per.Bcris l)) := by
    rw [Subtype.range_coe, ← (Pi.basisFun (Per.Bcris l) (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, hsum j]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h1 : v j i ∈ Submodule.span (↥(K0 K)) b := by
      rw [hspanb]; exact Submodule.subset_span ⟨⟨j, i⟩, rfl⟩
    exact Submodule.span_le_restrictScalars (↥(K0 K)) (Per.Bcris l) b h1
  let bb := Module.Basis.mk hliB hsp
  have hcard : Fintype.card b = d := by
    rw [← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]
  let e : b ≃ Fin d := Fintype.equivFinOfCardEq hcard
  let bd := bb.reindex e
  refine ⟨(Pi.basisFun (Per.Bcris l) (Fin d)).toMatrix bd, bd.toMatrix (Pi.basisFun (Per.Bcris l) (Fin d)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext i j
  have hx := congrFun (hvb (e.symm j) g) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, bd, bb] using hx

end GlobalTheory.Per.PerMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBasis
section
noncomputable section

namespace GlobalTheory.NL.LetterFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i : ZMod n) (a : LetA O n) : (letE i : LetA O n) * a = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem single_mul_letE (i : ZMod n) (a : PowerSeries O) :
    (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i :=
  single_mul_letE i 1

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  rw [letE_mul]
  simp [letE, h]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem sum_letE_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem lettersDecompose [NeZero n] : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose W T := by
  refine ⟨?_, le_antisymm (iSup_le fun i x hx => ((mem_Nl_iff W T i x).1 hx).1) fun x hx => ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hk : (⨆ (j) (_ : j ≠ i), W.Nl T j) ≤
        LinearMap.ker (LinearMap.lsmul (LetA O n) (W.DD T) (letE i)) := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← ((mem_Nl_iff W T j y).1 hy).2, smul_smul,
        letE_mul_ne hj.symm, zero_smul]
    have h0 := hk hx'
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ((mem_Nl_iff W T i x).1 hx).2] at h0
    exact h0
  · rw [← sum_letE_smul W T x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, hx, rfl⟩

theorem isLetterBasis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis W T i (fun k => (letE i : LetA O n) • (b k : W.DD T)) := by
  have hli : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (W.N T).ker_subtype
  refine ⟨fun k => ⟨b k, (b k).2, rfl⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hy' : y = ∑ k, b.repr ⟨y, hy⟩ k • (b k : W.DD T) := by
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this.symm
  generalize b.repr ⟨y, hy⟩ = a at hy'
  subst hy'
  have key : (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) =
      ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, letE_mul]
  refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _
    rw [key]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, single_mul_letE]
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _ at hc
    rw [key] at hc
    simp only [smul_smul, single_mul_letE] at hc
    funext k
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
    have h1 := congrFun h0 i
    simpa [sub_eq_zero] using h1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule

theorem exists_letter_basis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    ∃ c : Module.Basis (Fin r) (PowerSeries O) ↥(W.Nl T i),
      ∀ k, (c k : W.DD T) = (letE i : LetA O n) • (b k : W.DD T) := by
  obtain ⟨hm, hu⟩ := isLetterBasis W T b i
  let f : Fin r → ↥(W.Nl T i) := fun k => ⟨_, hm k⟩
  have hs : ∀ c : Fin r → PowerSeries O, ((∑ k, c k • f k : ↥(W.Nl T i)) : W.DD T) =
      ∑ k, (Pi.single i (c k) : LetA O n) • (letE i : LetA O n) • (b k : W.DD T) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul W T i (c k) (f k)
  have hli : LinearIndependent (PowerSeries O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := hs c
    rw [hc] at h1
    have h2 := (hu 0 (Submodule.zero_mem _)).unique h1 (y₂ := fun _ => 0) (by simp)
    exact congrFun h2 k
  have hsp : ⊤ ≤ Submodule.span (PowerSeries O) (Set.range f) := by
    intro x _
    obtain ⟨c, hc, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hs c).trans hc.symm)⟩
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

end Generic

theorem letters_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose (H.W K s LL h) T ∧ GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersFree (H.W K s LL h) T ∧
      ∀ i, ∃ b : Fin (Module.finrank ↥(OL LL) ↥T.L.T) → (H.W K s LL h).DD T,
        GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis (H.W K s LL h) T i b := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact ⟨lettersDecompose _ T, fun i => ⟨(exists_letter_basis _ T b i).choose⟩,
    fun i => ⟨_, isLetterBasis _ T b i⟩⟩

end GlobalTheory.NL.LetterFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfPowLeOfPowLeSameAdicTopology
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.exists_of_pow_le_of_pow_le :
    ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι)
      (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I →
      ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  intro S A _ _ s I ι TB I' n m _ _ _ h1 h2
  have hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k := fun k => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 k
  classical
  refine ⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩
  · intro x k
    exact (TB.fin x (n * k)).subset fun i hi h => hi (hk k h)
  · intro x k F hF
    set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG
    have hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k) := by
      intro i hi
      by_contra h
      exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hmain := TB.approx x (n * k) G hG'
    have hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s := Ideal.map_mono (hk k)
    have hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i =
        ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_union_left)]
    have hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have : i ∉ F := (Finset.mem_sdiff.1 hi).2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))
    have : x - ∑ i ∈ F, s (TB.c i x) * TB.b i =
        (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [hsplit]; ring
    rw [this]
    exact add_mem (hmap hmain) hrest
  · refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h1
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinear
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PairLine

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]

theorem cont_form {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (f : V →ₗ[LL] LL) : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

theorem cont_act {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (ρ : Representation LL G V)
    (hρ : ∀ x, Continuous fun g => ρ g x) : Continuous fun p : G × V => ρ p.1 p.2 := by
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let b := Module.finBasis LL V
  have h : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.repr p.2 i • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_snd).smul
    ((hρ (b i)).comp continuous_fst)

theorem cont_bil {V V' : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] [AddCommGroup V'] [Module LL V']
    [FiniteDimensional LL V'] [TopologicalSpace V'] [IsModuleTopology LL V']
    (m : V →ₗ[LL] V' →ₗ[LL] LL) : Continuous fun q : V × V' => m q.1 q.2 := by
  let b := Module.finBasis LL V
  have h : (fun q : V × V' => m q.1 q.2) = fun q => ∑ i, b.repr q.1 i * m (b i) q.2 := by
    funext q
    conv_lhs => rw [← b.sum_repr q.1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
    ((cont_form (m (b i))).comp continuous_snd)

end Cont

theorem exists_pair : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨Z, inv, hZ, hinv⟩ := GlobalTheory.InvLine.exists_inv hT l P K LL O hO
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hmem : ∀ (a : ↥(continuousCocycles A.ρ)) (b : ↥(continuousCocycles A'.ρ)), cupL A'.ρ m a.1 b.1 ∈ Z := by
    intro a b
    obtain ⟨ha, ha'⟩ : Continuous a.1 ∧ ∀ g h, a.1 (g * h) = a.1 g + A.ρ g (a.1 h) := a.2
    obtain ⟨hb, hb'⟩ : Continuous b.1 ∧ ∀ g h, b.1 (g * h) = b.1 g + A'.ρ g (b.1 h) := b.2
    rw [hZ]
    refine ⟨?_, fun g h k => ?_⟩
    · have h1 : Continuous fun p : ↥(GK K) × ↥(GK K) => A'.ρ p.1 (b.1 p.2) :=
        (cont_act A'.ρ A'.cont).comp (continuous_fst.prodMk (hb.comp continuous_snd))
      exact (cont_bil m).comp ((ha.comp continuous_fst).prodMk h1)
    · simp only [cupL]
      rw [← hm.1 g (a.1 h) (A'.ρ h (b.1 k)), ha', hb', map_mul, Module.End.mul_apply]
      simp only [map_add (f := _), LinearMap.add_apply]
      ring
  refine ⟨LinearMap.mk₂ LL (fun a b => inv ⟨cupL A'.ρ m a.1 b.1, hmem a b⟩) ?_ ?_ ?_ ?_,
    fun a b => ?_⟩
  · intro a a' b
    rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro a b b'
    rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · rw [LinearMap.mk₂_apply]
    exact hinv _

end GlobalTheory.PairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDenseOffFinite
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.MainNotions.V

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.frob_dense_off_finite : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (T : Set (HeightOneSpectrum (𝓞 F))), T.Finite →
    Dense {σ : _root_.Formalism.ConjugateSelfDual.G F Ω | ∃ v : HeightOneSpectrum (𝓞 F), v ∉ T ∧ ∃ A : ValuationSubring Ω,
      _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) σ} := by
  intro F Ω _ _ _ _ _ T hT
  refine (_root_.GlobalTheory.Published.chebotarevDegreeOne'.dense
    (F := F) (Ω := Ω) hT).mono ?_
  rintro σ ⟨v, hv, -, A, hA, hσ⟩
  exact ⟨v, hv, A, hA, hσ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinfStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_lift_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Tail.tail | exact GlobalTheory.ExpImage.Tail.tail | (intros; apply GlobalTheory.ExpImage.Tail.tail <;> assumption)
end

