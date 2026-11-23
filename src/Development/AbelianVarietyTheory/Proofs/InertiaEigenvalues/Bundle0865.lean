module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0740

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

def padInt {m n : ℕ} (_h : m ≤ n) (v : Fin m → ℤ) : Fin n → ℤ :=
  fun i => if hi : (i : ℕ) < m then v ⟨i, hi⟩ else 0

theorem padInt_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (padInt h) := by
  intro v w hvw
  funext j
  have := congrFun hvw ⟨j, lt_of_lt_of_le j.2 h⟩
  simpa [padInt, j.2] using this

theorem padInt_zero {m n : ℕ} (h : m ≤ n) : padInt h (0 : Fin m → ℤ) = 0 := by
  funext i; simp only [padInt, Pi.zero_apply]; split_ifs <;> rfl

theorem padInt_valid {m n : ℕ} (h : m ≤ n) {v : Fin m → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    (∀ i, 0 ≤ padInt h v i) ∧ Antitone (padInt h v) := by
  have hnn : ∀ i, 0 ≤ padInt h v i := by
    intro i; unfold padInt; split_ifs
    · exact hv.1 _
    · exact le_rfl
  refine ⟨hnn, fun a b hab => ?_⟩
  by_cases hb : (b : ℕ) < m
  · have ha : (a : ℕ) < m := lt_of_le_of_lt hab hb
    simp only [padInt, ha, hb, dite_true]
    exact hv.2 (show (⟨a, ha⟩ : Fin m) ≤ ⟨b, hb⟩ from hab)
  · have : padInt h v b = 0 := by simp [padInt, hb]
    rw [this]; exact hnn a

theorem toNat_padInt {m n : ℕ} (h : m ≤ n) (v : Fin m → ℤ) :
    (fun i => (padInt h v i).toNat) = padNat (n := n) (fun i => (v i).toNat) := by
  funext i; simp only [padInt, padNat]; split_ifs <;> simp

theorem sum_padNat {m n : ℕ} (h : m ≤ n) (l : Fin m → ℕ) : ∑ i, padNat (n := n) l i = ∑ i, l i := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro c hc
    have : ¬ (c : ℕ) < m := fun hcm => hc ⟨⟨c, hcm⟩, Fin.ext rfl⟩
    simp [padNat, this]
  · intro i; simp [padNat, i.2]

theorem norm_rsTermNM_le (q : ℕ) (hq : 0 < q) {m n : ℕ} (h : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (v : Fin m → ℤ) :
    ‖rsTermNM q α β x v‖ ≤ (sqTerm q α x (padInt h v) + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTermNM, if_pos hv, sqTerm, if_pos (padInt_valid h hv), sqTerm, if_pos hv, toNat_padInt h v,
      sum_padNat h, norm_mul, norm_mul, Complex.norm_conj, norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ -
      ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTermNM, if_neg hv, norm_zero]
    exact div_nonneg (add_nonneg (sqTerm_nonneg _ _ _ _) (sqTerm_nonneg _ _ _ _)) zero_le_two

theorem rsTermNM_zero (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) : rsTermNM q α β x 0 = 1 := by
  have h : (fun _ : Fin m => (0 : ℕ)) = fun i => ((0 : Fin m → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (padNat (n := n) fun i => ((0 : Fin m → ℤ) i).toNat) α = 1 := by
    rw [← h]
    have : (padNat (n := n) fun _ : Fin m => (0 : ℕ)) = fun _ => 0 := padNat_zero
    rw [this, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin m → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

theorem rsTermNM_partVec (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (l : {l : Fin m → ℕ // Antitone l}) :
    rsTermNM q α β x (partVec l) =
      schurAt (padNat (n := n) l.1) α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTermNM, if_pos (partVec_valid l)]
  simp [partVec]

end GlobalTheory.RSnmEul

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

theorem hasSum_rsTermNM_local (q : ℕ) {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin m → ℤ => ‖rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin m → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin m → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hpad : ∀ l : Fin m → ℕ, padTo hmn l = padNat (n := n) l := fun l => rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL hmn α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := m)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTermNM, if_neg hval]

theorem euler_rsTermNM : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  intro I q n m hmn α β x _ hq hα hβ
  set f : I → (Fin m → ℤ) → ℂ := fun i v => rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v
    with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTermNM_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hinj : Function.Injective fun p : I × {v : Fin m → ℤ // v ≠ 0} =>
      ((p.1, ⟨padInt hmn p.2.1, fun h0 => p.2.2 (padInt_injective hmn (h0.trans (padInt_zero hmn).symm))⟩) :
        I × {v : Fin n → ℤ // v ≠ 0}) := by
    intro p p' hp
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hp
    exact Prod.ext hp.1 (Subtype.ext (padInt_injective hmn hp.2))
  have hA' := hA.comp_injective hinj
  have hsum : Summable fun p : I × {v : Fin m → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef, Function.comp_apply] using norm_rsTermNM_le (q p.1) (by have := hq p.1; omega) hmn
          (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA'.add hB).div_const 2)
  obtain ⟨hN, hP, -⟩ := GlobalTheory.EulerSum.euler_product_intVec m f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTermNM_local (q i) hmn (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  refine ⟨∑' l : I →₀ (Fin m → ℤ), l.prod f, ?_, hN.of_norm.hasSum⟩
  simpa only [hloc] using hP

end GlobalTheory.RSnmEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFourierGaussLattice
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.FourierCell

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors SchwartzMap

variable {E : Type} [Field E] [NumberField E]

theorem finId_val (u : (Af E)ˣ) :
    ((finId E u : (Ad E)ˣ) : Ad E) = ((1, (u : Af E)) : InfiniteAdeleRing E × Af E) := by
  change (1 - sFin E 1 + sFin E (u : Af E) : Ad E) = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change (1 : Af E) - 1 + (u : Af E) = u
    simp

theorem mem_one_iff (x : Af E) :
    x ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ↔ ∀ v, Valued.v (pLoc E v x) ≤ 1 := by
  simp only [mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rfl

theorem val_zpow_unif {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (n : ℤ) :
    Valued.v (ϖ ^ n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, h, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem ofAdd_le_one_iff (n : ℤ) :
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

theorem exists_fourier_gauss_lattice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y₀ : Fin (m + 1) → Ad E),
    (∀ w ∉ S, ∀ j, pLoc E w (pFin E (y₀ j)) ∈ w.adicCompletionIntegers E) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
      Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) ∧
      (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧
        (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) ∧
      0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y₀).re ∧
      ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
      ∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) =
          GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0) := by
  intro E _ _ _ m S y₀ hy₀
  classical
  let φ : 𝓢(Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidean (E := Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E))
      (GroundTheory.Global.gaussianSchwartz _)
  have hφ : ∀ x, φ x = ((Real.exp (-Real.pi * ‖toEuclidean x‖ ^ 2) : ℝ) : ℂ) := fun x => by
    simp [φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  let g : (Fin (m + 1) → Af E) → ℂ := finiteTensor fun j => cosetIndicator 1 (pFin E (y₀ j))
  have hg : g ∈ finiteSchwartzBruhatPi E :=
    finiteTensor_mem fun j => cosetIndicator_mem_finiteSchwartzBruhat _ _
  let G := schwartzBruhatTensorPi φ g
  have hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin (m + 1)) := schwartzBruhatTensorPi_mem φ hg
  have hG1 := adelicFourierPi_mem_schwartzBruhatPi hG
  have hG2 := adelicFourierPi_mem_schwartzBruhatPi hG1
  have hG3 := adelicFourierPi_mem_schwartzBruhatPi hG2
  have hFG : adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) = G := by
    rw [adelicFourierPi_adelicFourierPi hG2, adelicFourierPi_adelicFourierPi hG]
    funext x
    simp
  have hGv : ∀ y, G y = φ (infPartPi y) *
      if ∀ j v, Valued.v (pLoc E v (pFin E (y j)) - pLoc E v (pFin E (y₀ j))) ≤ 1 then 1 else 0 := by
    intro y
    simp only [G, g, schwartzBruhatTensorPi, finiteTensor, cosetIndicator_apply, Finset.prod_boole,
      Finset.mem_univ, true_implies, mem_one_iff, map_sub]
    rfl
  refine ⟨adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G)), hG3, ?_, ?_, ?_, ?_⟩
  · rw [hFG]; exact continuous_of_mem_schwartzBruhatPi hG
  · intro y
    rw [hFG, hGv, hφ]
    split_ifs
    · rw [mul_one]
      exact ⟨by rw [Complex.ofReal_re]; exact (Real.exp_pos _).le, Complex.ofReal_im _⟩
    · rw [mul_zero]
      exact ⟨le_refl _, rfl⟩
  · rw [hFG, hGv, hφ, if_pos (fun j v => by simp)]
    rw [mul_one, Complex.ofReal_re]
    exact Real.exp_pos _
  · intro ϖ hϖ a ha y hy
    have hFy : ∀ z, adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) z = G z :=
      fun z => by rw [hFG]
    have hinf : infPartPi (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = infPartPi y := by
      funext j
      simp only [infPartPi, finId_val]
      congr 1
      change (1 : InfiniteAdeleRing E) * (y j).1 = (y j).1
      exact one_mul _
    have hfin : ∀ j v, pLoc E v (pFin E (((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j)) =
        ((ϖ v : v.adicCompletion E) ^ a v) * pLoc E v (pFin E (y j)) := by
      intro j v
      rw [map_mul, map_mul, finId_val]
      change ((ϖ v ^ a v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * _ = _
      rw [Units.val_zpow_eq_zpow_val]
    have hint : ∀ w ∉ S, ∀ j, Valued.v (pLoc E w (pFin E (y₀ j))) ≤ 1 := fun w hw j => by
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hy₀ w hw j
    constructor
    · intro hpos
      rw [hFy, hFy, hGv, hGv, hinf]
      congr 1
      refine if_congr ?_ rfl rfl
      refine forall_congr' fun j => forall_congr' fun v => ?_
      rw [hfin]
      by_cases hv : v ∈ S
      · rw [ha v hv, zpow_zero, one_mul]
      · have h1 := hint v hv j
        have h2 : Valued.v (pLoc E v (pFin E (y j))) ≤ 1 := by
          simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using (hy v hv).1 j
        have h3 : Valued.v ((ϖ v : v.adicCompletion E) ^ a v) ≤ 1 := by
          rw [val_zpow_unif (hϖ v), ofAdd_le_one_iff]
          linarith [hpos v]
        have key : ∀ t, Valued.v t ≤ 1 → Valued.v (t - pLoc E v (pFin E (y₀ j))) ≤ 1 :=
          fun t ht => (Valuation.map_sub _ _ _).trans (max_le ht h1)
        exact iff_of_true (key _ (by rw [map_mul]; exact mul_le_one' h3 h2)) (key _ h2)
    · rintro ⟨w, hw⟩
      rw [hFy, hGv, if_neg, mul_zero]
      intro hP
      have hwS : w ∉ S := fun h => by rw [ha w h] at hw; exact lt_irrefl _ hw
      obtain ⟨j, hj⟩ := (hy w hwS).2
      have h1 := hint w hwS j
      have h := hP j w
      rw [hfin] at h
      have ht : Valued.v ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j))) ≤ 1 := by
        have h4 := Valuation.map_add Valued.v
          ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j)) - pLoc E w (pFin E (y₀ j)))
          (pLoc E w (pFin E (y₀ j)))
        rw [sub_add_cancel] at h4
        exact h4.trans (max_le h h1)
      rw [map_mul, hj, mul_one, val_zpow_unif (hϖ w), ofAdd_le_one_iff] at ht
      omega

end GlobalTheory.FourierCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement
section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_whittaker_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  first | (exact @GlobalTheory.SchurEquiv.schurF_equivariant) | (exact GlobalTheory.SchurEquiv.schurF_equivariant) | (intros; apply GlobalTheory.SchurEquiv.schurF_equivariant <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := by
  first
  | exact @GlobalTheory.SchurExtCpt.exists_compact_support
  | exact GlobalTheory.SchurExtCpt.exists_compact_support
  | (intros; apply GlobalTheory.SchurExtCpt.exists_compact_support <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.schur_function_smooth_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  first | (exact @GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (exact GlobalTheory.SchurExt.schurF_mul_finGL_eq) | (intros; apply GlobalTheory.SchurExt.schurF_mul_finGL_eq <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.SchurExt
open scoped Topology

namespace GlobalTheory.SchurExt.Parts

theorem L_glob : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := GlobalTheory.T.exists_smooth_whittakerBump_adelicGL

theorem L_equiv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := GlobalTheory.Tx.schur_function_whittaker_equivariant

theorem L_cpt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := GlobalTheory.Tx.schur_function_compact_support_modulo_unipotent

theorem L_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := GlobalTheory.Tx.schur_function_smooth_right_invariant

theorem L_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := GlobalTheory.T.contDiffOn_chart_schurComplementExtension

theorem L_block : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply

theorem L_projNA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := a), prS S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ prO S a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) ∧ GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := GlobalTheory.T.adelicGLProjections_upperUnitriangular_genericChar

theorem L_projSupS : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := GlobalTheory.T.adelicGLProjections_on_supportedAtPlaces

theorem L_projInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL

theorem L_projFin : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := GlobalTheory.T.eventually_adelicGLProjections_finite_near_one

theorem L_blockSupS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S := GlobalTheory.T.blockDiagGL_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.Parts
open GlobalTheory.SchurExt.Parts

theorem GlobalTheory.SchurExt.exists_ext : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  intro E _ _ _ m r S β hβN hβC hβU hβS
  obtain ⟨b₁, h1one, h1N, h1C, h1U, h1S⟩ := L_glob E r
  obtain ⟨Φ, hΦ1, hΦN, -, ⟨UΦ, hUΦo, hUΦ⟩, -⟩ := GlobalTheory.WhitBump.exists_bump E (m + r + 1) S
  let f : ContDiffBump (0 : Fin (r + 1) → Fin (m + 1) → Cinf E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC, hCp⟩ := L_cpt E m r S β b₁ f hβC h1C f.hasCompactSupport
  obtain ⟨W, hW, hWk⟩ := L_inv E m r S β b₁ f hβU hβC h1U h1C
  refine ⟨extB S β b₁ f Φ, ?_, ⟨C, hC, ?_⟩, ?_, ?_, ?_⟩
  · intro u hu g
    obtain ⟨h1, h2, h3⟩ := L_projNA E (m + r + 1 + 1) S u hu
    simp only [extB, map_mul]
    rw [L_equiv E m r β b₁ f hβN h1N _ h1, hΦN _ h2, ← h3]
    ring
  · intro p hp hne
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 p hp.1
    refine hCp p hp fun h0 => hne ?_
    simp only [extB, e1, e2, h0, zero_mul]
  · let U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)) :=
      { carrier := {k | ∀ g, extB S β b₁ f Φ (g * finGL E _ k) = extB S β b₁ f Φ g}
        mul_mem' := fun {a b} ha hb g => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, ← mul_assoc, hb, ha]
        one_mem' := fun g => by simp only [map_one, mul_one]
        inv_mem' := fun {a} ha g => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          have := ha (g * finGL E _ a⁻¹)
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
          exact this.symm }
    refine ⟨U, Subgroup.isOpen_of_mem_nhds U (g := 1) ?_, fun u hu g => hu g⟩
    have hV' : (UΦ : Set _) ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)) := hUΦo.mem_nhds UΦ.one_mem
    filter_upwards [L_projFin E _ S W _ hW hV'] with k hk
    obtain ⟨⟨k', hk'W, hk'⟩, ⟨k'', hk''V, hk''⟩⟩ := hk
    intro g
    simp only [extB, map_mul, hk', hk'']
    rw [hWk k' hk'W (hk' ▸ (L_projSupS E _ S).2 _) _ ((L_projSupS E _ S).2 g), hUΦ k'' hk''V]
  · intro g
    have hs := (L_smooth E m r β b₁ f hβS h1S h1C f.contDiff (prS S _ g)).mul
      (contDiffOn_const (c := Φ (prO S _ g)))
    refine hs.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    obtain ⟨e1, e2⟩ := L_projInf E _ S g hx'.unit
    simp only [chart, dif_pos hx', extB, e1, e2]
  · intro h hh
    obtain ⟨e1, e2⟩ := (L_projSupS E _ S).1 _ (L_blockSupS E m r S h hh)
    have hf0 : f 0 = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    simp only [extB, e1, e2, hΦ1, mul_one, L_block, h1one, hf0, Complex.ofReal_one]
end

