module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphPoints
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

namespace ContractMixed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def PrefixPull (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) {n : ℕ} (L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') :
    Prop :=
  ∃ (h : p ≤ n) (L : Fin p → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (L j)) ∧
    ∀ j, IsPullHerm κ v (L j) (L' (Fin.castLE h j))


omit [∀ k, Fintype (ι' k)] in
theorem PrefixPull.mono {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by
  obtain ⟨hpn, L, hL, hLL⟩ := h
  exact ⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩


omit [∀ k, Fintype (ι' k)] in
theorem PrefixPull.init {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p n : ℕ} {L' : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'}
    (h : PrefixPull κ v p L') (hpn : p ≤ n) : PrefixPull κ v p (Fin.init L') := by
  obtain ⟨_, L, hL, hLL⟩ := h
  exact ⟨hpn, L, hL, fun j => hLL j⟩

theorem arInt_eq_zero (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by
  obtain ⟨h, L, hL, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL

theorem geoNum_eq_zero (hVert : PFVert.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    {s : MRing ι'} {a : K' → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (hsP : s ∉ P') {W : Ideal (MRing ι')}
    (hW : W ∈ divSupp P' s) (hh : ¬ IsHorizontal W) : geoNum n W (fun j => (L' j).a) = 0 := by
  obtain ⟨h, L, -, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh

theorem aux (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) (I : AllFam) (hI : I.IsFamily) {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n p : ℕ) (P' : Ideal (MRing ι')) (d₀ : ℕ) (L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d₀ → d₀ < p → PrefixPull κ v p L' →
      (∀ j, IsSmoothHerm (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero =>
    intro p _ d₀ _ _ _ hdp hpre _
    obtain ⟨h, -⟩ := hpre
    omega
  | succ n ih =>
    intro p P' d₀ L' hP' hQ hdp hpre hL'
    classical
    rcases Nat.lt_or_ge n p with hnp | hpn
    ·
      obtain ⟨h, L, hL, hLL⟩ := hpre
      have hp : p = n + 1 := by omega
      subst hp
      have e : (fun j => L' (Fin.castLE h j)) = L' := funext fun j => congrArg L' (Fin.ext rfl)
      have key := hC I hI K ι K' ι' κ v P' d₀ (n + 1) L (fun j => L' (Fin.castLE h j)) hv hP' hQ hdp hL hLL
      rwa [e] at key
    ·
      have hpre0 : PrefixPull κ v p (Fin.init L') := hpre.init hpn
      have hL0 : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
      have hPp : P'.IsPrime := hP'.2.1.1
      choose i hi using hP'.2.1.2.2

      have key : ∀ B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι', IsSmoothHerm B' → (∀ k, 0 ≤ B'.a k) →
          I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
        intro B' hB' hBa
        let b : K' → ℕ := fun k => (B'.a k).toNat
        let s : MRing ι' := ∏ k, X ⟨k, i k⟩ ^ b k
        have hs : s ∉ P' := by
          intro h
          obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).1 h
          exact hi k (hPp.mem_of_pow_mem _ hk)
        have hsm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b := by
          convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι' k)) b using 1
          funext k
          simp [Finset.sum_filter]
        have hBa' : ∀ k, B'.a k = b k := fun k => (Int.toNat_of_nonneg (hBa k)).symm
        have hsec : IsSectionOn P' B' s := ⟨b, hBa', hsm, hs⟩
        rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b hP' hL0 hB' hBa' hsm hs, recR_eq]
        have h1 : arInt P' s B' (Fin.init L') = 0 :=
          arInt_eq_zero hInt hv hP' hQ (hpre0.mono hdp.le) B' s
        have h2 : cycR (I K' ι') P' (Fin.init L') s = 0 := by
          unfold cycR
          refine (finsum_mem_congr rfl fun W hW => ?_).trans (finsum_mem_zero _)
          split_ifs with hH
          · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
            obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
            have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
            have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
            have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
              (Ideal.Quotient.factor_surjective hle)
            rw [hQW.2.2.2, hQ.2.2.2] at hdim
            have hlt : dW + Fintype.card K ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
            rw [ih p W dW (Fin.init L') hWn hQW (by omega) hpre0 hL0, mul_zero]
          · rw [geoNum_eq_zero hVert hv hP' hQ (hpre0.mono hdp.le) hsm hs hW hH]
            simp
        rw [h1, h2, sub_zero]

      let A' := L' (Fin.last n)
      let M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι' := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric fun k => (-(A'.a k)).toNat
      have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
      have hA' : IsSmoothHerm A' := hL' _
      have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M hP' hL0 hA' hM
      have h3 := key (A'.tensor M) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hM) fun k => by
        show 0 ≤ A'.a k + ((-(A'.a k)).toNat : ℤ)
        omega
      have h4 := key M hM fun k => by
        show (0 : ℤ) ≤ ((-(A'.a k)).toNat : ℤ)
        omega
      have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
      rw [e]
      linarith

theorem of_contract (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d₀ d r L L' N hv hP' hQ hdd hL hLL hN
  refine aux hC hIm hInt hVert I hI hv (d + r) d P' d₀ (Fin.append L' N) hP' hQ hdd ?_ ?_
  · refine ⟨Nat.le_add_right d r, L, hL, fun j => ?_⟩
    have e : Fin.castLE (Nat.le_add_right d r) j = Fin.castAdd r j := rfl
    rw [e, Fin.append_left]
    exact hLL j
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact IsPullHerm.isSmoothHerm hv (hLL i) (hL i)
    · rw [Fin.append_right]
      exact hN i

theorem of_found (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (hInt : PFIntZero.Statement) (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement :=
  of_contract (contract_of hIm hF hV) hIm hInt hVert

end ContractMixed

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordRatioDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordRatioDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (Φ' : Type) [Field Φ'] [CharZero Φ'] (x' : (Σ k', ι' k') → Φ'),
    IsBlockMap κ v → RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Φ') = mCoordIdeal y →
    IntermediateField.relfinrank (blockFnField (x' ∘ v)) (blockFnField x') =
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.FibreMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FibreMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P'),
    IsBlockMap κ v → IsMultiHomogIdeal P' → IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenFibreChartDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GenFibreChartDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    [CharZero G.Φ'] (c : ∀ k, ι k) (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k, G.x ⟨k, c k⟩ ≠ 0) → (∀ k, G.x' ⟨k.1, i k⟩ ≠ 0) →
    Module.finrank G.Φ (IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) =
      IntermediateField.relfinrank (blockFnField (G.x' ∘ v)) (blockFnField G.x')

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem imageArith : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement :=
  ImageArith.of_found BlockTrdeg.proof

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing multAt divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat map_eq_maximalIdeal_of_isRadical)

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem localMult_map_intCast_complex {τ : Type} [Fintype τ] (J W : Ideal (MvPolynomial τ ℤ)) [W.IsPrime]
    (W'' : Ideal (MvPolynomial τ ℂ)) (hW'' : W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    localMult (J.map (MvPolynomial.map (Int.castRingHom ℂ))) W'' = localMult J W := by
  have := HilbertSamuel.mvPolynomial_int_complex_flat τ
  have hAlg := HilbertSamuel.algebraMap_mvPolynomial_int_complex τ
  have : W''.IsPrime := hW''.1.1
  have hc : W''.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W :=
    HilbertSamuel.ComplexMinimalPrimesContract.proof τ W ‹_› W'' hW''
  have : W''.LiesOver W := ⟨by rw [Ideal.under, hAlg, hc]⟩
  have hrad := HilbertSamuel.PrimeComplexRadical.proof τ W ‹_›
  have key := localMult_map_of_flat J W W''
    (by rw [hAlg]; exact map_eq_maximalIdeal_of_isRadical hrad hW'')
  rwa [hAlg] at key

theorem multAt_eq_localMult {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (J W : Ideal (MRing ι))
    [W.IsPrime] : multAt J W = localMult J W := by
  unfold multAt localMult
  rw [dite_eq_left ‹_›, dite_eq_left ‹_›, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]

theorem ChartSectionLength.proof (hComp : ChartConeComponent.Statement) (hLen : ChartConeLength.Statement) :
    ChartSectionLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have : W.IsPrime := hW.1.1.1
  obtain ⟨W'', hW'', hle⟩ := hComp K ι W m σ i hWa.2.1 W' hW'
  rw [hLen K ι P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle, multAt_eq_localMult,
    localMult_map_intCast_complex _ W W'' hW'']

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongChartLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre mcPts
  isOpen_blockNonzero)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartComponents mem_segreChartComponents chartLift
  contDiff_chartLift chartLift_blockNonzero segre_chartLift chart_coord_eq_one)

theorem LelongChartLimit.proof (hInt : SegreChartIntegral.Statement) (hDim : SegreChartDim.Statement)
    (hNot : ChartSectionNotMem.Statement) (hLel : LelongPolyLimit.Statement)
    (hDiv : ChartDivisorCompare.Statement) : LelongChartLimit.Statement := by
  classical
  intro K _ _ ι _ P n L A s g i δ hP hL hA hs hg hδ hsupp
  obtain ⟨a, ha, hsa, -⟩ := id hs
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let G := fun x => χ x * g (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  let kk := fun x => A.h (lam x)
  let F := fun (ε : ℝ) x => Real.log (‖eval x (chartSection σ i s)‖ ^ 2 + ε * kk x ^ 2) / 2
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i
  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'
  have hxΩ : ∀ x ∈ segreChartSet P σ i, x ∈ Ω := by
    rintro _ ⟨z, -, hzi, rfl⟩
    exact chartLift_blockNonzero σ i (by simp [σ, hzi])

  have key : ∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [G, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [G, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)

  have hlim := tendsto_finsetSum (segreChartComponents P σ i) fun J hJs =>
    hLel _ n J (chartSection σ i s) G kk Φ (mem_segreChartComponents.1 hJs).1.1
      (hDim K ι P (n + 1) _ σ i hP J hJs) (hNot K ι P (n + 1) _ σ i A s hP hs J hJs)
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm g hg.1)⟩ χ.hasCompactSupport.mul_right
      (fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩) ⟨Ω, hΩ, hJ J hJs, hsm _ hA⟩
      fun x hx => A.pos _ (hJ J hJs hx)
  rw [hDiv K ι P n _ σ i L A s g δ G Φ hP hL hs hg hδ hsupp
    fun x hx => ⟨key x hx, fun j => EventuallyEq.rfl⟩] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)

  set M := (regLine A s ε ha hsa).tensor A
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) :=
    fun j => Fin.cases ((isSmoothHerm_regLine hA hε ha hsa).mul hA) (fun i => hL i) j
  have hcongr : ptsIntegral P
      (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
        (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  beta_reduce
  rw [hcongr]
  refine (hInt K ι P n _ σ i (Fin.cons M L) g δ G (Matrix.vecCons (F ε) Φ) hP hML hg hδ (Or.inl hsupp)
    fun x hx => ⟨key x hx, fun j => ?_⟩).symm
  refine Fin.cases ?_ (fun j => EventuallyEq.rfl) j
  filter_upwards [hΩ.mem_nhds (hxΩ x hx)] with y hy
  simp only [Matrix.cons_val_zero, Function.comp_apply, Inter.PtsAddFirst.pot_cons, Fin.cons_zero, F, kk,
    eval_chartSection]
  exact (log_regLine_tensor A s hε ha hsa (lam y) hy).symm

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftBlockDatum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel LiftBlockGraph

noncomputable section

theorem LiftBlockDatum.proof (hE : ResExistsStatement) (hVol : ResVolume.Statement)
    (hPts : LiftGraphPoints.Statement) (hMet : LiftGraphMetric.Statement) : LiftBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D N P0 a ι' _ x' hD harith _ hP0 hsemi hconj _ hx' hgen hbir'
  have hv : ∀ j, liftCoords x' j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hgv := generatesOn_liftCoords y (a • N.a) x' hgen
  have harith' := isArithVar_addBlock y (a • N.a) (liftCoords x') harith hv hgv
  obtain ⟨A, hAdeg, hAconj, hAsemi, hrel⟩ :=
    hMet K ι Ω y N P0 a (Fintype.card ι') (liftCoords x') hP0 hsemi hconj hv hgv
  have hnot : ¬ (⊤ : Ideal (MRing (addIdx ι (Fintype.card ι')))) ≤ mCoordIdeal (addBlock y (liftCoords x')) :=
    fun h => harith'.2.1.1.ne_top (top_le_iff.mp h)
  obtain ⟨J, -, -, -, ⟨R⟩⟩ := hE (Option K) (addIdx ι (Fintype.card ι')) _ ⊤ D harith'
    isMultiHomogIdeal_top hnot
  let _ : MeasurableSpace R.toAnRes.X := borel _
  have : BorelSpace R.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hVol (Option K) (addIdx ι (Fintype.card ι')) _ J D R.toAnRes harith'
  refine ⟨
    { y := addBlock y (liftCoords x'), k₀ := none, A := A, P0 := mCoordIdeal (addBlock y (liftCoords x')),
      J := J, R := R.toAnRes, meas := borel _, borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := harith',
      birat := blockBirational_addBlock y x' hbir', deg := hAdeg, conjInv := hAconj, normalForm_baseLattice_le_dualSpan_sup_line := le_rfl,
      semipos := hAsemi, vol := hdV }, rfl, rfl, hrel, ?_⟩
  exact hPts K ι Ω y (a • N.a) (Fintype.card ι') (liftCoords x') hv hgv

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

def GoodChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) →
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

