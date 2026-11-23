module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesLatticeTrivialQuotient
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.MooreDeterminant

variable {B Q : Type} [CommRing B] [IsDomain B] [Field Q] [Algebra Q B]

theorem det_mem (S : B → Prop) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι B) (hM : ∀ i j, S (M i j)) : S M.det := by
  rw [Matrix.det_apply]
  have hz : S 0 := by simpa using h0 0
  refine Finset.sum_induction _ S hadd hz ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply hmul
  · have := h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)
    simpa using this
  · have h1 : S 1 := by simpa using h0 1
    exact Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)

theorem iter_eq (φ : B →+* B) (m : ℕ) : ⇑(φ ^ m) = (⇑φ)^[m] := RingHom.coe_pow φ m

theorem moore_core (φ : B →+* B) (S : B → Prop)
    (hφ : ∀ b, S b → S (φ b)) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    (L : B) (hL : φ L = L) (h : ℕ)
    (ratio : ∀ s, s < h → ∀ ω ω' : B, S ω → S ω' → φ^[h] ω = L ^ s * ω → φ^[h] ω' = L ^ s * ω' → ω' ≠ 0 →
      φ ω * ω' = ω * φ ω' → ∃ c : Q, ω = c • ω') :
    ∀ (n : ℕ) (a : Fin (n + 1) → B), n + 1 ≤ h → (∀ j, S (a j)) → (∀ j, φ^[h] (a j) = L * a j) →
      LinearIndependent Q a → (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a j)).det ≠ 0 := by
  have hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b) := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [Function.iterate_succ_apply']; exact hφ _ (ih b hb)
  intro n
  induction n with
  | zero =>
    intro a _ _ _ ha
    rw [Matrix.det_fin_one]
    simpa using ha.ne_zero 0
  | succ n ih =>
    intro a hk hSa hfa ha hdet
    set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef

    have hA := ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _)
      (ha.comp _ (Fin.castSucc_injective _))
    set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef
    have hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det := by
      simp [ω, Fin.succAbove_last]
    have hωl0 : ω (Fin.last _) ≠ 0 := by rw [hωl]; exact hA
    have hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_last, Fin.succAbove_last, ω]
      congr 2
    have hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m) := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]
      simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
      rw [RingHom.map_det]
      congr 2
      ext i j
      simp [M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']
    have hK : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0 := fun i c => by
      have := congrFun (congrFun hK i) c
      simpa [Matrix.mul_apply] using this

    set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 -
      M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef
    have hv : ∀ i, ∑ m, M i m * v m = 0 := by
      intro i
      have e1 := hker i 0
      have e2 := hker i (Fin.last _)
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      have : ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) =
          M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) =
          M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all
    have hvl : v (Fin.last _) = 0 := by simp only [v]; ring
    have hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0 := by
      funext i
      have := hv (Fin.castSucc i)
      rw [Fin.sum_univ_castSucc, hvl, mul_zero, add_zero] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hA hv'
    have hvall : ∀ m, v m = 0 := by
      intro m
      refine Fin.lastCases hvl (fun j => ?_) m
      exact congrFun hv0 j

    have hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _)) := by
      intro m
      have E := hvall m
      simp only [v, hu, hw, Fin.val_last, pow_add] at E
      have hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      have he : ((-1 : B) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      linear_combination ((-1 : B) ^ (m : ℕ)) * E
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he

    have hSω : ∀ m, S (ω m) := fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))
    have hLi : ∀ i : ℕ, φ^[i] L = L := fun i => Function.iterate_fixed hL i
    have hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m := by
      intro m
      rw [← iter_eq, hωdef]
      simp only
      rw [RingHom.map_det]
      have : (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) =
          L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]
        rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]
      rw [this, Matrix.det_smul, Fintype.card_fin]

    have hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _) := fun m =>
      ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)
    choose c hc using hrat

    have hrow := hker 0 (Fin.last _)
    set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd
    have hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0 := by
      rw [← hrow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hu, hc m]
      simp only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow,
        map_neg, map_one]
      ring
    have hsum0 : ∑ m, d m • a m = 0 := (mul_eq_zero.1 hsum).resolve_right hωl0
    have hdl := Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)
    have hcl : c (Fin.last _) = 0 := by
      simp only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl
      exact hdl
    apply hωl0
    rw [hc (Fin.last _), hcl, zero_smul]

end GlobalTheory.PMon.MooreDeterminant

namespace GlobalTheory.PMon

theorem moore_statement : Moore := by
  intro l _ P AI T h k hk a hPa hfa ha
  obtain ⟨hF, hinj, -⟩ := _root_.GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨hpφ, -, hpR, hpQ, -⟩ := _root_.GlobalTheory.PMon.CrisPlus.plus_props l P AI T
  haveI : IsDomain P.R.BdR := hF.isDomain
  haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj
  cases k with
  | zero => simp
  | succ n =>
    exact GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ
      (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h
      (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => _root_.GlobalTheory.PMon.ratio_holds l P AI T h s hs ω ω' h1 h2 h3 h4 h5 h6)
      n a hk hPa hfa ha

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem locAway_φ_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) :
    ∀ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f),
      D.φ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f) := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    exact Submonoid.subset_closure ⟨m + 1, by simp only [Function.iterate_succ_apply']⟩
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem locAway_iterate_sub_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (m : ℕ) :
    D.φ^[m] f - f ^ (l ^ m) ∈ Ideal.span {(l : A)} := by
  rw [← Ideal.Quotient.eq]
  induction m with
  | zero => simp
  | succ m ih =>
    have hl0 : ((l : A ⧸ Ideal.span {(l : A)})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [Function.iterate_succ_apply', D.φ_eq, map_add (f := _), map_mul, map_pow, ih, map_natCast, hl0, zero_mul,
      add_zero, map_pow, map_pow, ← pow_mul, pow_succ]

theorem locAway_dvd_mod {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (J : Ideal A)
    (hl : (l : A) ∈ J) (n : ℕ) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f), ∃ (k : ℕ) (t : A), f ^ k - s * t ∈ J ^ n := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    have h1 : f ^ (l ^ m) - D.φ^[m] f ∈ J := by
      rw [← neg_sub, neg_mem_iff]
      exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 hl)) (locAway_iterate_sub_mem D f m)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (f ^ (l ^ m)) (f ^ (l ^ m) - D.φ^[m] f) n
    refine ⟨l ^ m * n, t, ?_⟩
    have e : f ^ (l ^ m * n) - D.φ^[m] f * t = (f ^ (l ^ m) - D.φ^[m] f) ^ n := by
      rw [pow_mul]
      have e2 : f ^ l ^ m - (f ^ l ^ m - D.φ^[m] f) = D.φ^[m] f := by ring
      rw [e2] at ht
      linear_combination ht
    rw [e]; exact Ideal.pow_mem_pow h1 n
  | one => exact ⟨0, 1, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, t1, h1⟩ := hx
    obtain ⟨k2, t2, h2⟩ := hy
    refine ⟨k1 + k2, t1 * t2, ?_⟩
    have e : f ^ (k1 + k2) - x * y * (t1 * t2) = f ^ k1 * (f ^ k2 - y * t2) + y * t2 * (f ^ k1 - x * t1) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)

theorem locAway_units {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} (g : Hom B C) (f : B.A)
    (hu : IsUnit (g.f f)) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f), IsUnit (g.f s) := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      show IsUnit (g.f (B.D.φ^[m + 1] f))
      change IsUnit (g.f (B.D.φ^[m] f)) at ih
      rw [Function.iterate_succ_apply', g.f_φ]
      exact ih.map C.D.φ
  | one => rw [map_one]; exact isUnit_one
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem GenAway₂ : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A),
    GenAway B f d → Nonempty (LocP B f d) := by
  intro l _ R _ B f d hg
  set M := Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f) with hM
  have hfM : f ∈ M := Submonoid.subset_closure ⟨0, rfl⟩
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_localization l B.A B.D M (locAway_φ_mem B.D f)
  obtain ⟨hIL, hdnz, N, hN⟩ := GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion l R B f d hg M hfM
  set J : Ideal (Localization M) := Ideal.span {(l : Localization M)} ⊔
    Ideal.span {algebraMap B.A (Localization M) d} with hJdef
  have hJ : (JJ B).map (algebraMap B.A (Localization M)) = J := by
    rw [JJ, Ideal.map_sup, hIL, Ideal.map_span, Set.image_singleton, map_natCast]
  have hJfg : J.FG := Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)
  obtain ⟨Q, _, i, hi⟩ := _root_.GlobalTheory.BSP.isCompl_exists _ J hJfg
  have hlJ : (l : Localization M) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨DQ, hDQ⟩ := _root_.GlobalTheory.BSP.exists_delta_completion l _ Q i J hi hlJ DL
  obtain ⟨hqnz, hqN⟩ := _root_.GlobalTheory.BSP.ComplLD.regular_and_torsion_bounded l _ Q i (algebraMap B.A (Localization M) d) N hdnz hN hi
  set g : B.A →+* Q := i.comp (algebraMap B.A (Localization M)) with hgdef
  have hgδ : ∀ x, g (B.D.δ x) = DQ.δ (g x) := fun x => by
    simp only [hgdef, RingHom.comp_apply]; rw [hDL x, hDQ]
  have hIg : B.I.map g = Ideal.span {g d} := by
    rw [hgdef, ← Ideal.map_map, hIL, Ideal.map_span, Set.image_singleton]; rfl
  have hIle : B.I ≤ (Ideal.span {g d}).comap g := Ideal.map_le_iff_le_comap.1 hIg.le
  have hJi : J.map i = Ideal.span {(l : Q)} ⊔ Ideal.span {g d} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      map_natCast]; rfl
  have hcomp : IsAdicComplete (Ideal.span {(l : Q)} ⊔ Ideal.span {g d}) Q := by
    have := hi.complete; rwa [hJi] at this
  have hgφ : g.comp B.D.φ = DQ.φ.comp g := RingHom.ext fun x => Delta.map_φ_of_map_δ B.D DQ g hgδ x
  have hlmem : (l : Q) ∈ Ideal.span {g d} ⊔ (Ideal.span {g d}).map DQ.φ := by
    have h := Ideal.mem_map_of_mem g B.l_mem
    have hgm : (B.I.map B.D.φ).map g = (B.I.map g).map DQ.φ := by
      rw [Ideal.map_map, Ideal.map_map, hgφ]
    rwa [map_natCast, Ideal.map_sup, hgm, hIg] at h
  have hbdd : ∃ n : ℕ, ∀ x : Q ⧸ Ideal.span {g d}, (∃ m : ℕ, (l : Q ⧸ Ideal.span {g d}) ^ m * x = 0) →
      (l : Q ⧸ Ideal.span {g d}) ^ n * x = 0 := by
    refine ⟨N, fun x ⟨m, hm⟩ => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
    exact hqN y m hm
  let Qo : Obj l R :=
    { A := Q
      D := DQ
      I := Ideal.span {g d}
      inv := invertible_span_singleton hqnz
      complete := hcomp
      l_mem := hlmem
      bdd := hbdd
      str := (Ideal.quotientMap (Ideal.span {g d}) g hIle).comp B.str }
  let inl : Hom B Qo :=
    { f := g
      f_δ := hgδ
      f_I := fun x hx => hIle hx
      f_str := fun r x h => by
        show _ = Ideal.quotientMap (Ideal.span {g d}) g hIle (B.str r)
        rw [← h, Ideal.quotientMap_mk] }
  have hlu : ∀ s : M, IsUnit (g s) := fun s => (IsLocalization.map_units (Localization M) s).map i
  have hJn : ∀ n : ℕ, ((JJ B) ^ n).map g = (J ^ n).map i := fun n => by
    rw [hgdef, ← Ideal.map_map, Ideal.map_pow, hJ]
  have hlJB : (l : B.A) ∈ JJ B := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨{ Q := Qo, inl := inl, unit := ?_, I_eq := rfl, univ := ?_, surj := ?_, ker := ?_ }⟩
  · exact hlu ⟨f, hfM⟩
  · intro C gC hu
    have hMu : ∀ s : M, IsUnit (gC.f s) := fun s => locAway_units gC f hu s s.2
    set lift : Localization M →+* C.A := IsLocalization.lift hMu with hliftdef
    have hla : ∀ x, lift (algebraMap B.A (Localization M) x) = gC.f x := IsLocalization.lift_eq hMu
    have hδl : IsδMap DL C.D lift := by
      have e : (W2.map lift).comp (deltaSectionToWittLengthTwo DL) = (deltaSectionToWittLengthTwo C.D).comp lift := by
        apply IsLocalization.ringHom_ext M
        refine RingHom.ext fun x => W2.ext rfl ?_
        change lift (DL.δ (algebraMap B.A (Localization M) x)) =
          C.D.δ (lift (algebraMap B.A (Localization M) x))
        rw [← hDL x, hla, hla, gC.f_δ]
      intro x; exact congrArg W2.snd (RingHom.congr_fun e x)
    have hJle : J.map lift ≤ JJ C := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        map_natCast, hla]
      exact sup_le_sup_left (Ideal.span_le.2 (Set.singleton_subset_iff.2 (gC.f_I d hg.1))) _
    haveI := C.complete
    have hhaus : IsHausdorff (JJ C) C.A := inferInstance
    obtain ⟨h, hh⟩ := _root_.GlobalTheory.BSP.exists_ringHom_comp_of_isCompl _ Q C.A i J (JJ C) hi C.complete lift hJle
    have hhi : ∀ y, h (i y) = lift y := fun y => RingHom.congr_fun hh y
    have hδh : IsδMap DQ C.D h := by
      refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C.A DQ C.D (J.map i) (JJ C) h ?_ ?_ hhaus ?_
      · rw [← map_natCast i]; exact Ideal.mem_map_of_mem i hlJ
      · rw [Ideal.map_map, hh]; exact hJle
      · intro x n
        obtain ⟨y, hy⟩ := hi.surj x n
        refine ⟨i y, mem_δLocus.2 ?_, by rwa [← Ideal.map_pow]⟩
        rw [← hDQ y, hhi, hhi, hδl]
    have hgC : h.comp g = gC.f := by rw [hgdef, ← RingHom.comp_assoc, hh, IsLocalization.lift_comp]
    have hIC : ∀ x ∈ Ideal.span {g d}, h x ∈ C.I := fun x hx =>
      (Ideal.span_le (I := C.I.comap h)).2 (Set.singleton_subset_iff.2 (by
        show h (g d) ∈ C.I
        rw [← RingHom.comp_apply h g, hgC]; exact gC.f_I d hg.1)) hx
    let H : Hom Qo C :=
      { f := h
        f_δ := hδh
        f_I := hIC
        f_str := fun r x hx => by
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B.str r)
          change Ideal.Quotient.mk _ x = Ideal.quotientMap _ g hIle (B.str r) at hx
          rw [← hb, Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
          rw [← gC.f_str r b hb, Ideal.Quotient.eq, ← hgC, RingHom.comp_apply, ← map_sub]
          exact hIC _ hx }
    refine ⟨H, Hom.ext' hgC, fun y hy => Hom.ext' ?_⟩
    have hy' : y.f.comp g = gC.f := congrArg Hom.f hy
    have hyi : y.f.comp i = h.comp i := IsLocalization.ringHom_ext M (hy'.trans hgC.symm)
    exact GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap _ Q C.A i J (JJ C) hi hhaus y.f h (by rw [hyi, hh]; exact hJle) hyi
  · intro x n
    obtain ⟨y, hy⟩ := hi.surj x n
    obtain ⟨⟨b0, s⟩, hbs⟩ := IsLocalization.mk'_surjective M y
    dsimp only at hbs
    subst hbs
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n s s.2
    refine ⟨k, b0 * t, ?_⟩
    change g f ^ k * x - g (b0 * t) ∈ ((JJ B) ^ n).map g
    have hs : i (IsLocalization.mk' (Localization M) b0 s) * g s = g b0 := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have e : g f ^ k * x - g (b0 * t) = g f ^ k * (x - i (IsLocalization.mk' (Localization M) b0 s)) +
        i (IsLocalization.mk' (Localization M) b0 s) * g (f ^ k - s * t) := by
      rw [map_sub, map_mul, map_mul, map_pow]; linear_combination (g t) * hs
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem g hkt))
    rw [hJn]; exact hy
  · intro b n hb
    change g b ∈ ((JJ B) ^ n).map g at hb
    rw [hJn] at hb
    have h1 := hi.ker _ n hb
    rw [← hJ, ← Ideal.map_pow] at h1
    obtain ⟨⟨⟨j, hj⟩, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff M (Localization M)).1 h1
    rw [← map_mul] at hjs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 hjs
    have hcs : ((c : B.A) * (s : B.A)) * b ∈ JJ B ^ n := by
      have e : ((c : B.A) * (s : B.A)) * b = (c : B.A) * j := by rw [← hc]; ring
      rw [e]; exact Ideal.mul_mem_left _ _ hj
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n ((c : B.A) * (s : B.A)) (M.mul_mem c.2 s.2)
    refine ⟨k, ?_⟩
    have e : f ^ k * b = (f ^ k - ((c : B.A) * (s : B.A)) * t) * b + t * (((c : B.A) * (s : B.A)) * b) := by ring
    rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hkt) (Ideal.mul_mem_left _ _ hcs)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOfIsRootMinpolyUnramifiedRootsOfUnityField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem conj_norm_eq_of_minpoly_root :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  intro l _ a _ z z' h
  have hint : IsIntegral (↥(Kunr l a)) z := Algebra.IsIntegral.isIntegral z
  have hm : minpoly (↥(Kunr l a)) z' = minpoly (↥(Kunr l a)) z :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)).symm
  obtain ⟨τ, hτ⟩ := ((Normal.minpoly_eq_iff_mem_orbit (Om l)).1 hm)
  have hτ' : τ • z = z' := hτ
  rw [← hτ']
  exact (spectralNorm_eq_of_equiv (τ.restrictScalars ℚ_[l]) z).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiModuleHomShortExactSplitWittTiltStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧ (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  first | exact @GlobalTheory.phiModuleHom_shortExact_split_wittTilt | exact GlobalTheory.phiModuleHom_shortExact_split_wittTilt | (intros; apply GlobalTheory.phiModuleHom_shortExact_split_wittTilt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismPushoutModAdicPow_universal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → ∀ (Q : Obj l R) (a : Hom C Q) (b : Hom B' Q), a.comp h = b.comp k → ∃! c : Hom C' Q, c.comp k' = a ∧ c.comp h' = b := by
  first | exact @GlobalTheory.BSP.PoUniv.isPO_univ | exact GlobalTheory.BSP.PoUniv.isPO_univ | (intros; apply GlobalTheory.BSP.PoUniv.isPO_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlockStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_mulVec_through_first_block : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K) (ε : Matrix (Fin r) (Fin r) K), (∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) → F.rank = ε.rank := by
  first | exact @GlobalTheory.rank_eq_of_acts_through_first_block | exact GlobalTheory.rank_eq_of_acts_through_first_block | (intros; apply GlobalTheory.rank_eq_of_acts_through_first_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesLatticeTrivialQuotientStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ses_lattice_trivial_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (e : ℕ) (Yt T Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L) (hle : Gj K s ≤ GK K), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → IsCrysOn S S.W.GKs Yt → ∀ yt ∈ Yt.L.T, ∀ f : S.G → ↥T.L.T, (∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → letI := zlMod LL T; ∃ k : ℕ, IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) := by
  first | exact @GlobalTheory.Adopt.ses_lattice_trivial_quotient | exact GlobalTheory.Adopt.ses_lattice_trivial_quotient | (intros; apply GlobalTheory.Adopt.ses_lattice_trivial_quotient <;> assumption)
end

