module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

variable {n d : ℕ}

theorem logLogCut_mem_Icc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold logLogCut cutStep
  split_ifs
  · simp
  · simp
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem comp_sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (g : (Fin d → ℂ) → ℝ) :
    (fun w => g (A *ᵥ s w)) =ᶠ[𝓝 (A *ᵥ x)] g := by
  obtain ⟨U, hU, hxU, -, -, hsec, -⟩ := hs
  filter_upwards [hU.mem_nhds hxU] with w hw
  rw [(hsec w hw).1]

theorem maDens_cons_of_hessC_eq_smul {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by
  have e : ∀ u : (Fin (D + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons u ψ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ) k) y) =
        Fin.cons (hessC u y) (fun k => hessC (ψ k) y) := fun u => by
    funext k; exact Fin.cases rfl (fun i => rfl) k
  have hm := mdisc_update_smul
    (Fin.cons (hessC g y) (fun k => hessC (ψ k) y) : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    0 (c : ℂ) (hessC g y)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at hm
  unfold maDens
  rw [e, e, h, hm, Complex.re_ofReal_mul]
  ring

theorem vecCons_comp {D : ℕ} (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ)
    (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) :
    (fun k => (vecCons f φ : Fin (D + 1) → (Fin n → ℂ) → ℝ) k ∘ s) = Fin.cons (f ∘ s) (fun k => φ k ∘ s) := by
  funext k; exact Fin.cases rfl (fun i => rfl) k

theorem sheetSum_le_mul {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) (c : ℝ)
    (F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s → F x s ≤ c * G x s) :
    sheetSum J A F y ≤ c * sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp

theorem term_le_of_hessC {D : ℕ} {X : Type*} (B : Set X) (w t : X → ℝ) (x : X)
    (hw : |w x| ≤ 1) (hwB : x ∉ B → w x = 0) (ht : 0 ≤ t x) (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) {c e : ℝ}
    (h : hessC f y = (e : ℂ) • hessC g y) (he : |e| ≤ c * t x) :
    |w x * maDens (Fin.cons f ψ) y| ≤ c * |B.indicator t x * maDens (Fin.cons g ψ) y| := by
  rw [maDens_cons_of_hessC_eq_smul f g ψ y e h]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht]
    have hM := abs_nonneg (maDens (Fin.cons g ψ) y)
    calc |w x| * (|e| * |maDens (Fin.cons g ψ) y|) ≤ 1 * (c * t x * |maDens (Fin.cons g ψ) y|) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right he hM) (by positivity) zero_le_one
      _ = c * (t x * |maDens (Fin.cons g ψ) y|) := by ring
  · rw [hwB hx, zero_mul, abs_zero, Set.indicator_of_notMem hx, zero_mul, abs_zero, mul_zero]

theorem CutOffGradient.proof (hH : LogLogCutHess.Statement) : CutOffGradient.Statement := by
  obtain ⟨K, hK0, hK⟩ := hH
  refine ⟨K, fun n d J A P R φ k y hJ hdim hA => ?_⟩
  have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  obtain ⟨a, b, ha, hb, hHa, hHb⟩ := hK (d + 1) P k y
  have hc : 0 ≤ K / ((k : ℝ) + 1) := by positivity
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  have ht : ∀ x, 0 ≤ tubeWeight P (A *ᵥ x) := fun x => by
    unfold tubeWeight; split_ifs <;> positivity

  have key : ∀ (w : (Fin n → ℂ) → ℝ) (g : (Fin (d + 1) → ℂ) → ℝ) (e : ℝ),
      (∀ x, |w x| ≤ 1) → (∀ x, x ∉ B → w x = 0) →
      hessC g y = (e : ℂ) • hessC (fun z => logAbsSq P z ^ 2 / 2) y →
      |e| ≤ K / ((k : ℝ) + 1) * tubeWeight P y →
      chartAbsDens J A w (vecCons (fun x => g (A *ᵥ x)) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y := by
    intro w g e hw hwB hg he
    unfold chartAbsDens tubeDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    have hy : A *ᵥ x = y := hx.2
    rw [vecCons_comp, vecCons_comp]
    refine term_le_of_hessC B w (fun x => tubeWeight P (A *ᵥ x)) x (hw x) (hwB x) (ht x) _ _ _ y ?_
      (by rw [hy]; exact he)
    rw [← hy, Function.comp_def, Function.comp_def, hessC_congr' (comp_sheet_eventuallyEq hs g),
      hessC_congr' (comp_sheet_eventuallyEq hs fun z => logAbsSq P z ^ 2 / 2), hy, hg]
  have h1 : ∀ x, |B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    unfold Set.indicator; split_ifs <;> simp
  have h0 : ∀ x, x ∉ B → B.indicator (fun _ => (1 : ℝ)) x = 0 := fun x hx => Set.indicator_of_notMem hx _
  refine ⟨key _ (logLogCut P k) a h1 h0 hHa ha, key _ (fun z => logLogCut P k z ^ 2 / 2) b h1 h0 hHb hb,
    key _ (logLogCut P k) a (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _) hHa ha⟩
  unfold Set.indicator
  split_ifs
  · have hm := logLogCut_mem_Icc P k (A *ᵥ x)
    show |logLogCut P k (A *ᵥ x)| ≤ 1
    rw [abs_of_nonneg hm.1]; exact hm.2
  · simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }

theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorGeneralPointBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }

theorem proof (hOne : DivisorOneComponent.Statement) (hBr : DivisorBranches.Statement) :
    DivisorGeneralPointBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hOne n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hBr n d J u hJ hdim hu
  refine ⟨I₁ ⊓ I₂, le_inf hle₁ hle₂, quotient_inf_dim_lt hdim₁ hdim₂, ?_⟩
  intro q hqJ hqu hqI
  have hq₁ : q ∉ zeroSet I₁ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).1
  have hq₂ : q ∉ zeroSet I₂ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).2
  obtain ⟨W, hW, hqW, huniq, hnear⟩ := hI₁ q hqJ hqu hq₁
  obtain ⟨m, γ, ord, π, hcov, ⟨N, hN, hsl⟩, hpair, hord, hbij⟩ := hI₂ q hqJ hqu hq₂
  refine ⟨W, hW, hqW, huniq, hnear, m, γ, ord, π, hcov, ⟨N, hN, fun b x hx => ?_⟩, hpair, hord, hbij⟩
  have hKW : J ⊔ Ideal.span {linForm u} ≤ W := hW.1.2
  refine hsl x ⟨fun f hf => hx.1 f (hKW (Ideal.mem_sup_left hf)), hx.2⟩ ?_ b
  have hx0 := hx.1 _ (hKW (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using hx0

end DivisorGeneralPointBranches

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorRegularGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem DivisorRegularGeneric.proof (hG : FrameGraphGeneric.Statement) : DivisorRegularGeneric.Statement := by
  classical
  intro n d J u hJ hdim hu
  set L : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {linForm u} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W => hfinM.mem_toFinset
  have hevL : ∀ x : Fin n → ℂ, eval x (linForm u) = linEval u x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [linForm, linEval, map_sum]

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one hu hW (fun h => by
      rw [hdim] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdim] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  choose! hh hhW hhchart using fun W (hW : W ∈ L.minimalPrimes) =>
    graphChart_of_frameGraphGeneric hG W hW.1.1 (hdimW W hW)

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin n) ℂ := fun W => ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set f : MvPolynomial (Fin n) ℂ := ∑ W ∈ T, hh W * e W with hf
  have hsplit : ∀ W ∈ T, f = hh W * e W + ∑ V ∈ T.erase W, hh V * e V := fun W hW =>
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, hh V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV => Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hfW : ∀ W ∈ L.minimalPrimes, f ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hhW W hW h
    · exact heW W hW h

  have hcomp : ∀ x ∈ zeroSet J, linEval u x = 0 → ∃ W ∈ L.minimalPrimes, x ∈ zeroSet W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp => RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hevL] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp => RingHom.mem_ker.mp (hWx hp)⟩
  have hcompInv : ∀ W ∈ L.minimalPrimes, ∀ x ∈ zeroSet W, x ∈ zeroSet J ∧ linEval u x = 0 := by
    intro W hW x hx
    refine ⟨fun p hp => hx p (hW.1.2 (Ideal.mem_sup_left hp)), ?_⟩
    rw [← hevL]
    exact hx _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨L ⊔ Ideal.span {f}, le_sup_left, ringKrullDim_quotient_sup_span_lt hfW hdimW, ?_⟩
  intro q hqJ hqu hqI
  obtain ⟨W, hW, hqW⟩ := hcomp q hqJ hqu
  have hfq : eval q f ≠ 0 := by
    intro h0
    refine hqI fun p hp => ?_
    have hle : L ⊔ Ideal.span {f} ≤ RingHom.ker (eval q) := by
      refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr (by simpa using h0))
      obtain ⟨V, hV, hqV⟩ := hcomp q hqJ hqu
      exact RingHom.mem_ker.mpr (hqV p (hV.1.2 hp))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hqW _ (hrest W hW), add_zero, map_mul] at hfq
  refine graphChart_of_eq_on_open (U := {x | eval x (e W) ≠ 0})
    (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const) (right_ne_zero_of_mul hfq) ?_
    (hhchart W hW q hqW (left_ne_zero_of_mul hfq))
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxu⟩, hxe⟩
    refine ⟨?_, hxe⟩
    obtain ⟨V, hV, hxV⟩ := hcomp x hxJ hxu
    by_cases hVW : V = W
    · exact hVW ▸ hxV
    · exact absurd (hxV _ (heV W hW V hV (Ne.symm hVW))) hxe
  · rintro ⟨hxW, hxe⟩
    exact ⟨hcompInv W hW x hxW, hxe⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermWeierstrassDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem WeierstrassDivision.proof (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassPolynomialDivision.Statement) : WeierstrassDivision.Statement := by
  intro σ _ d f g hf hg hord
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d f hf hord
  obtain ⟨q, a, hq, ha, hgq⟩ := hD σ d c g hc hc0 hg
  refine ⟨fun x => q x / e x, a, hq.div he he0, ha, ?_⟩
  filter_upwards [hfe, hgq, he.continuousAt.eventually_ne he0] with x hfx hgx hex
  rw [hgx, hfx, div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hex]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularDimGe.proof (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  have hy : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hy
  set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef
  have hU : IsOpen U := hg₁.continuousOn.isOpen_inter_preimage hO₁ hV
  have hUne : U.Nonempty := ⟨t₀, ht₀, hyV⟩
  have hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U :=
    A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)

  have hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u := by
    intro t ht
    have h1 : g₁ t ∈ X ∩ V₁ := hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1
    have h2 : g₁ t ∈ X ∩ V := ⟨h1.1, ht.2⟩
    rw [hXV] at h2
    obtain ⟨u, hu, hgu⟩ := h2
    exact ⟨u, hu, hgu.symm⟩
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff
  apply hz
  refine Set.Subsingleton.finite ?_
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨u₁, hu₁, hg1⟩ := hmem t₁ ht₁.1
  obtain ⟨u₂, hu₂, hg2⟩ := hmem t₂ ht₂.1
  have hz1 : A' (g₁ t₁) = z := ht₁.2
  have hz2 : A' (g₁ t₂) = z := ht₂.2
  rw [hg1, hleft u₁ hu₁] at hz1
  rw [hg2, hleft u₂ hu₂] at hz2
  have hgg : g₁ t₁ = g₁ t₂ := by rw [hg1, hg2, hz1, hz2]
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem LocalOrder.proof (hL : SliceLength.Statement) (hS : SliceBranches.Statement)
    (hC : CurveBranchLength.Statement) : LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨U, hUo, hUd, hU⟩ := hL n d J W u hJ hdim hu hW
  obtain ⟨q, _, L, ⟨hrad, hlen⟩, c, hccov, hcdisj, hcord⟩ :=
    hS n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U
      (fun q => {L | IsRadicalAt (sliceIdeal J L q) q ∧
        localMult (J ⊔ Ideal.span {linForm u}) W =
          localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))})
      hUo hUd hU
  rw [hlen]
  exact hC n (sliceIdeal J L q) u q m c ord hrad hccov hcdisj hcord

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BranchLift.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : NormalModel J)
    (γ : GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    ∃ Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = zeroSetIn M.ideal ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

