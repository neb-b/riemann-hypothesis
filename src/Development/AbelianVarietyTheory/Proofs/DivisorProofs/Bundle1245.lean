module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFiniteStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_split_archimedean_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    ∃ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  first | exact @GlobalTheory.HeisSplit.rho_split | exact GlobalTheory.HeisSplit.rho_split | (intros; apply GlobalTheory.HeisSplit.rho_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeDegreeEqNegLogFrameHeight
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.FrameDeg

theorem form_eq_of_re_diag {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (F G : V → V → ℂ)
    (hFa : ∀ x y z, F x (y + z) = F x y + F x z) (hGa : ∀ x y z, G x (y + z) = G x y + G x z)
    (hFs : ∀ (a : K) x y, F x (a • y) = σ a * F x y) (hGs : ∀ (a : K) x y, G x (a • y) = σ a * G x y)
    (hFc : ∀ x y, starRingEnd ℂ (F x y) = F y x) (hGc : ∀ x y, starRingEnd ℂ (G x y) = G y x)
    (hd : ∀ x, (F x x).re = (G x x).re) (ha : ∃ a : K, (σ a).im ≠ 0) (x y : V) : F x y = G x y := by
  have hFl : ∀ x x' y, F (x + x') y = F x y + F x' y := by
    intro x x' y
    rw [← hFc y (x + x'), hFa, map_add (f := _), hFc, hFc]
  have hGl : ∀ x x' y, G (x + x') y = G x y + G x' y := by
    intro x x' y
    rw [← hGc y (x + x'), hGa, map_add (f := _), hGc, hGc]
  have hre : ∀ x y, (F x y).re = (G x y).re := by
    intro x y
    have h1 := hd (x + y)
    rw [hFl, hFa, hFa, hGl, hGa, hGa, ← hFc x y, ← hGc x y] at h1
    simp only [Complex.add_re, Complex.conj_re] at h1
    linarith [hd x, hd y]
  obtain ⟨a, ha⟩ := ha
  have h2 := hre x (a • y)
  rw [hFs, hGs, Complex.mul_re, Complex.mul_re, hre x y] at h2
  have him : (F x y).im = (G x y).im := by
    have : (σ a).im * (F x y).im = (σ a).im * (G x y).im := by linarith
    exact mul_left_cancel₀ ha this
  exact Complex.ext (hre x y) him

section Maj

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majAt_add_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y z : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + z) = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x z := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_conj (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    starRingEnd ℂ (Formalism.HermitianLatticesTheory.majAt b X v x y) = Formalism.HermitianLatticesTheory.majAt b X v y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.HermitianLatticesTheory.majAt, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_self_re (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) :
    (Formalism.HermitianLatticesTheory.majAt b X v x x).re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (by positivity)]
  simp only [Formalism.HermitianLatticesTheory.majAt, Complex.re_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Maj

theorem form_self_re_nonneg {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : 0 ≤ (nm.form σ x x).re := by
  open scoped ComplexOrder in
  by_cases hx : x = 0
  · subst hx
    have h0 : nm.form σ 0 0 = 0 := by
      have := nm.add_right σ 0 0 0
      simp only [add_zero] at this
      linear_combination -this
    simp [h0]
  · have hli : LinearIndependent K ![x] := by
      rw [linearIndependent_unique_iff]; simpa using hx
    have hp := (nm.posDef σ 1 ![x] hli).det_pos
    rw [Matrix.det_unique] at hp
    simpa using (Complex.pos_iff.1 hp).1.le

theorem finrank_eq_two_mul_nPl' {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end GlobalTheory.FrameDeg

namespace GlobalTheory.FrameDeg

theorem deg_eq_neg_log_ht : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [FiniteDimensional K V] (nm : HermFam K V), nm.IsConjInv → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) → (∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = nm.nrm v.embedding x) → ∀ L : Submodule (𝓞 K) V, L.FG → deg nm L = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ _ _ nm hinv ι _ _ b X hX hnorm L hL
  classical

  have hform : ∀ (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v x y = nm.form v.embedding x y := by
    intro v
    refine form_eq_of_re_diag v.embedding _ _ (majAt_add_right b X v) (nm.add_right _)
      (majAt_smul_right b X v) (nm.smul_right _) (majAt_conj b X v) (nm.conj_symm _) ?_ ?_
    · intro x
      rw [majAt_self_re, hnorm, HermFam.nrm, Real.sq_sqrt (form_self_re_nonneg nm _ x)]
    · have hc : v.IsComplex := IsTotallyComplex.isComplex v
      rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
      by_contra hall
      push_neg at hall
      apply hc
      ext a
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (hall a)
  obtain ⟨e, he⟩ := exists_isFrame L hL
  have hdeg := arakelovDegree_eq_degreeOfFamily nm hL he
  obtain ⟨hS, hSL⟩ := Formalism.HN.htGram K V ι b X hX _ e he.2.1
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact he.1 i)
  have hidx := hSL L hL hle rfl
  have hne := he.relIndex_ne_zero hL
  have hgram : ∀ v, Formalism.HN.gramPl b X v e = nm.gram v.embedding e := by
    intro v; ext a c; simp [Formalism.HN.gramPl, HermFam.gram, hform]
  open scoped ComplexOrder in
  have hpos : ∀ σ, 0 < (nm.gram σ e).det.re := fun σ =>
    (Complex.pos_iff.1 (Matrix.PosDef.det_pos (nm.posDef σ _ e he.2.1))).1
  have hsum : ∑ σ : K →+* ℂ, Real.log (nm.gram σ e).det.re =
      2 * ∑ w : InfinitePlace K, Real.log (nm.gram w.embedding e).det.re := by
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w),
        Real.log (nm.gram σ e).det.re = Real.log (nm.gram w.embedding e).det.re := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases InfinitePlace.mk_eq_iff.mp (hσ.2.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · rw [h]
      · rw [← h, det_gram_conj_re nm hinv]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
      (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
    push_cast; ring
  have hprod : 0 < ∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re :=
    Finset.prod_pos fun w _ => hpos _
  have hidx' : (0 : ℝ) < ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hht : Formalism.HN.ht b X L = (∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re) /
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    rw [eq_div_iff hidx'.ne', hidx, hS]
    exact Finset.prod_congr rfl fun w _ => by rw [hgram]
  rw [hdeg, degreeOfFamily, hsum, finrank_eq_two_mul_nPl', hht, Real.log_div hprod.ne' hidx'.ne',
    Real.log_prod (fun w _ => (hpos _).ne')]
  push_cast
  ring

end GlobalTheory.FrameDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariants
section
noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.HoweR.MultOne

variable {P Q R S : ℕ}

theorem coinv_stable2 (x : ℂ) (Y : Mat R S) {v : Pol P Q R S} (hv : v ∈ coinv P Q R S x) :
    fockAct2 P Q R S Y v ∈ coinv P Q R S x := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩
    rw [map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem fockHarmonicsSecondMember_of_jointShape_highestWeight {x : ℚ} {μ' : Ix R S → ℚ} (hJ : JointShape P Q R S (fun _ => x) μ') {f : Pol P Q R S}
    (h2 : f ∈ harm2 P Q R S) (hc : f ∈ GlobalTheory.FockScalarType.charSub P Q R S x)
    (hw : f ∈ hwSub (fockAct2 P Q R S) μ') : f ∈ harm1 P Q R S := by
  by_cases h0 : f = 0
  · subst h0; intro Z _; simp [minusPart]
  obtain ⟨d, hd, hdf⟩ := isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)
  have hdeg := (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2
  intro Z hZ
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]
  by_cases hd2 : d < 2
  · exact dnOp_low _ d hd2 f hdf
  by_contra hne
  have h1 := isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf)
    (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))
  rw [hdeg, ← hd] at h1
  have e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
  rw [e] at h1
  linarith

end GlobalTheory.HoweR.MultOne

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.MultOne in
theorem hw_le_span_sup_coinv : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' →
    ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  intro P Q R S x μ' hJ
  set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
    Submodule.span ℂ (jointHarm P Q R S) with hL
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)
  refine ⟨v.1, fun g hg => ?_⟩
  set C := coinv P Q R S (x : ℂ) with hC
  let pr := C.mkQ
  have hker : ∀ w, pr w = 0 ↔ w ∈ C := fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f := by
    intro X f
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)
  have hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w') := by
    intro Y w w' h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (hker _).2 (coinv_stable2 _ Y ((hker _).1 h))
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]
  obtain ⟨h, hh, hprh⟩ := GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := GlobalTheory.HarmLift.lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw
      exacts [hs1 X hX w hw, hs2 Y hY w hw])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw
      · rw [hpr1, hw, smul_zero]
      · rw [hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hprh] at hcpr
  have hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x := fun X hX =>
    hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])
  have hcw : c ∈ hwSub (fockAct2 P Q R S) μ' := by
    have hg2 := hg
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      refine hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_
      rw [hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      rw [hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0
        (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]
  have hcJ : c ∈ jointHarm P Q R S := ⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩
  have hcL : c ∈ L := by
    by_cases h0 : c = 0
    · rw [h0]; exact L.zero_mem
    exact ⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩
  obtain ⟨t, ht⟩ := hv ⟨c, hcL⟩
  have hct : c = t • v.1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have hgc : g - c ∈ C := (hker _).1 (by rw [map_sub, hcpr, sub_self])
  rw [← sub_add_cancel g c, add_comm]
  exact Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneSectionVanishingShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem vanishFrom_cut {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : L.Sec)
    [Mono (GlobalTheory.cutHom F hL t)] {j₀ : ℤ} (h : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) := by
  intro j hj q hq
  have hS := Twist.shortExact_map (Twist.isLB_lbZPow hL j) (shortExact_cutComplex F hL t)
  have e := Twist.twistZAddIso F hL (show (-1 : ℤ) + j = j - 1 by ring)
  letI := h (j - 1) (by omega) (q + 1) q.succ_pos
  exact cohOn.subsingleton₃ hS ⊤ q (h j (by omega) q hq)
    (cohOn.mapIso ℤ ⊤ (q + 1) e).injective.subsingleton

theorem vanishFrom_cut_and_hdim : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F] (t : L.Sec) [Mono (GlobalTheory.cutHom F hL t)] (j₀ : ℤ), VanishFrom L F j₀ → VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) ∧ ∀ j : ℤ, j₀ + 1 ≤ j → GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 = GlobalTheory.hdim k (GlobalTheory.twistZ F L (j - 1)) 0 + GlobalTheory.hdim k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) 0 := by
  intro k _ Y _ hY L hL F _ t _ j₀ h
  have hc := vanishFrom_cut hL F t h
  refine ⟨hc, fun j hj => ?_⟩
  have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k Y) F hY
  have hj' := Twist.isLB_lbZPow hL j
  have e := Twist.twistZAddIso F hL (show (-1 : ℤ) + j = j - 1 by ring)
  have key : chi k (GlobalTheory.twistZ F L j) =
      chi k (GlobalTheory.twistZ (GlobalTheory.twistZ F L (-1)) L j) + chi k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) :=
    have := chi_twist_shortExact (shortExact_cutComplex F hL t) hj'
      (hF.twist (Twist.isLB_lbZPow hL (-1)) _ hj') (hF.cut hL t _ hj')
    this
  have e₁ := (chi_congr k e).trans (chi_eq_hdim_zero k (h (j - 1) (by omega)))
  have e₂ := chi_eq_hdim_zero k (h j (by omega))
  have e₃ := chi_eq_hdim_zero k (hc j hj)
  exact Int.natCast_inj.1 (e₂.symm.trans (key.trans
    ((congrArg₂ (· + ·) e₁ e₃).trans (Nat.cast_add _ _).symm)))

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZeroStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (d : ι → Module.End ℂ V), (∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p)) →
    Φ₀ 1 ≠ 0 → Function.Injective Φ₀ := by
  first | exact @GlobalTheory.FockAlg.injective_of_pderiv | exact GlobalTheory.FockAlg.injective_of_pderiv | (intros; apply GlobalTheory.FockAlg.injective_of_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLiftSymbol
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.IntLift

variable {K : Type} [Field K] [NumberField K]

theorem mulPow_mem_global (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ} (h : j + a = l)
    (α : MonoDeg (Fin G.D) a) {m : G.Sec j} (hm : m ∈ G.global j) : mulPow G s h α m ∈ G.global l := by
  obtain ⟨F, rfl⟩ := hm
  refine ⟨(Vanishing.powChart (isLB_tens G.K.isLB G.isLBA) G.isLB ((Nat.cast_add j a).symm.trans (congrArg _ h))).mul
    (H0.ofSec G.str ⊤ (monoSec (G.sec s) α)) F, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec]
  rfl

end GlobalTheory.HSCore.IntLift

namespace GlobalTheory.HSCore

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalization
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem frame_normalise_integral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ)
    (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k) (hYQ : Y * Q' = 1) :
    ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k),
      (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  classical

  have key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det := by
    simp only [det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [hYQ, det_one] at key
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)
  haveI : Nonempty (Fin s → D) := ⟨p₀⟩
  obtain ⟨κ, hκ⟩ := Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)
  have hne : (Y.submatrix id κ).det ≠ 0 := by
    intro h0
    have := hκ p₀
    rw [h0, map_zero] at this
    exact right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))
  set h := (Y.submatrix id κ)⁻¹ with hh
  have hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p := by
    intro p; ext r c; simp [Matrix.mul_apply]
  have hone : (h * Y).submatrix id κ = 1 := by
    rw [hsub, hh]
    exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
  refine ⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩
  · intro i j
    have e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det := by
      have : (h * Y).submatrix id (Function.update κ i j) =
          (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j) := by
        ext r c
        by_cases hc : c = i
        · subst hc; simp
        · rw [updateCol_ne hc, ← hone]
          simp [Function.update_of_ne hc]
      rw [this, ← cramer_apply, cramer_one]; rfl
    rw [Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀]
    have hpos : 0 < valuation k (Y.submatrix id κ).det :=
      lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))
    rw [mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hκ _
  · intro i j
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · have : h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) =
        (h * Y).submatrix id κ := by
      ext r l; simp [Matrix.mul_apply]
    rw [this, hone]

end GlobalTheory
end

