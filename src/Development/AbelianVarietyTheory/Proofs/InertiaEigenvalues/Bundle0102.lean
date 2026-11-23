module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftWithLastBasis
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.MatchNotIm

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k (g : Matrix (Fin r) (Fin r) k) * full Y *
      embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, act, embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct])

theorem last_eq : (Fin.last r) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
  ext; simp

theorem embHom_last_row (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim j 0]; simp [embHom, Matrix.reindex_apply]

theorem embHom_last_col (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim i 0]; simp [embHom, Matrix.reindex_apply]

theorem conj_last (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by
  simp [Matrix.mul_apply, embHom_last_row, embHom_last_col]

theorem eL_dot (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    eL r k ⬝ᵥ (N *ᵥ eL r k) = N (Fin.last r) (Fin.last r) := by
  simp [eL, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem full_glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) :
    full (glMap φ Y) = (full Y).map φ := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [full, glMap, Matrix.reindex_apply]

end Alg

end GlobalTheory.JR.Step.MatchNotIm

namespace GlobalTheory.JR.Step.MatchNotIm

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by
  induction i with
  | zero => simp [hPQ]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * N ^ i * Q * (P * N * Q) = P * N ^ i * (Q * P) * N * Q := by simp only [Matrix.mul_assoc]
      _ = P * (N ^ i * N) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P]

theorem hasInv_liftH : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 →
    HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν _ _ hΔ hX
  have hΔ' : Delta (inv (glMap (algebraMap F E) Z)) ≠ 0 := by
    rw [InvMap.inv_glMap, InvMap.Delta_map]
    exact (map_ne_zero (algebraMap F E)).2 hΔ
  have hX' : inv X.toGl = inv (glMap (algebraMap F E) Z) := by
    rw [InvMap.inv_glMap]; exact hX
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (_root_.GlobalTheory.JR.normalForm_invariants E r).2.2.2.2 _ _ hΔ' hX'
  have hfull : full X.toGl = embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
    rw [← hg, full_act, full_glMap]
  have hPQ : embHom r E (g : Matrix (Fin r) (Fin r) E) * embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQP : embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * embHom r E (g : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : star (ν • eL r E) = star ν • eL r E := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, eL, Pi.single_apply, smul_eq_mul, star_mul']
    split_ifs <;> simp [mul_comm]
  replace hfull : full ((X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2) : Gl r E) =
      embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := hfull
  unfold HasInv
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift]
    rw [hfull]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift, mom]
    rw [hs, hfull, conj_pow _ _ _ hPQ hQP, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, eL_dot, eL_dot, conj_last]
    have hp : ((full Z).map (algebraMap F E)) ^ (i : ℕ) = ((full Z) ^ (i : ℕ)).map (algebraMap F E) := by
      have := map_pow (algebraMap F E).mapMatrix (full Z) (i : ℕ)
      simpa only [RingHom.mapMatrix_apply] using this.symm
    rw [hp, Matrix.map_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, ← hν]
    ring

end GlobalTheory.JR.Step.MatchNotIm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTest
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusAction
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem integral_comp_unit_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) [ν.IsAddHaarMeasure]
    (s : A.Kˣ) (g : A.K → ℂ) :
    ∫ b, g ((s : A.K) * b) ∂ν = ((A.absK (s : A.K) : ℂ))⁻¹ * ∫ b, g b ∂ν := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology A.K := by
    let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
    have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
    exact h.isEmbedding.secondCountableTopology
  have hme : MeasurableEmbedding (fun b : A.K => s • b) := (Homeomorph.smul s).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul ν s⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν) := by
    rw [hme.integral_map]; rfl
  have habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    congr 2
    ext; rfl
  rw [hint, hmap, integral_smul_measure, habs]
  simp [Complex.real_smul]

theorem pt_scale_eq_rg_mS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν hν ψ x s Φ
  funext p
  obtain ⟨a, u⟩ := p
  have hs0 : A.absK (s : A.K) ≠ 0 := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    exact_mod_cast (distribHaarChar_pos).ne'
  have key := integral_comp_unit_mul A ν s
    (fun b' => Φ (a * (s : A.K), b') * A.psiK ψ (x * b' * (u * ((s⁻¹ : A.Kˣ) : A.K))))
  simp only [pt, rg, mS, fourB, kx]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, mul_zero, add_zero, zero_add]
  rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hs0)] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e1 : x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u := by
    rw [show x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u * ((s : A.K) * ((s⁻¹ : A.Kˣ) : A.K)) by ring,
      Units.mul_inv, mul_one]
  simp only [e1, mul_comm a (s : A.K)]
  ring

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflection
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Hyp

theorem pt_pt_eq_reflect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  intro F E _ _ _ _ _ A ψ x ν hsd Φ hΦ

  haveI : T2Space A.K := by
    let e := (Module.finBasis F A.K).equivFun
    have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    first
      | exact T2Space.of_continuous_injective e.injective he
      | exact T2Space.of_injective_continuous e.injective he
      | exact e.injective.t2Space he
  funext p
  have hemb : Topology.IsClosedEmbedding (Prod.mk p.1 : A.K → A.K × A.K) := by
    refine ⟨isEmbedding_prodMkRight p.1, ?_⟩
    have : Set.range (Prod.mk p.1 : A.K → A.K × A.K) = ({p.1} : Set A.K) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      simp only [Set.mem_range, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      constructor
      · rintro ⟨y, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨b, rfl, rfl⟩
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  have hf : IsTest (fun b => Φ (p.1, b)) :=
    ⟨hΦ.1.comp_continuous hemb.continuous, hΦ.2.comp_isClosedEmbedding hemb⟩
  exact hsd.2 _ hf p.2

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem wHyp_wS_eq_fourB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  intro F E _ _ _ _ _ A ψ x e ν μ hpt hinv hrg hcc hci hker hlc hint φ hφ y
  set p := ci A e y with hp
  have hy : y = cc A e p := (hci y).symm
  have hG : IsTest (rg A (wS A.K) (pt A ν ψ x (fun q => φ (cc A e q)))) := hrg _ (hpt _ (hcc φ hφ))
  have hh : IsTest (fun y' => φ y' * A.kerL ψ x y' (cc A e p)) :=
    ⟨hφ.1.mul (hlc _), hφ.2.mul_right⟩
  unfold wHyp
  rw [hinv _ hG]
  rw [← hp]
  conv_rhs => rw [hy]
  unfold fourB
  rw [hint _ hh]
  simp only [pt, fourB, rg, wS, hker]
  simp
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  ring

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructure
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem coord_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  intro F E _ _ _ _ _ A e hee hse
  obtain ⟨-, hinj, hnorm, htr, -⟩ := Et.quadratic_structure F E A
  have htrs : ∀ (a : A.K) (f : A.L),
      Algebra.trace A.K A.L (algebraMap A.K A.L a * f) = a * Algebra.trace A.K A.L f := by
    intro a f
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hone : ∀ f : A.L, star f = 1 - f → Algebra.trace A.K A.L f = 1 := by
    intro f hf
    apply hinj
    rw [htr, hf, map_one]
    ring
  have hte : Algebra.trace A.K A.L e = 1 := hone e hse
  have htf : Algebra.trace A.K A.L (1 - e) = 1 :=
    hone (1 - e) (by rw [star_sub, star_one, hse])
  have hst : ∀ p : A.K × A.K, star (Hyp.cc A e p) =
      algebraMap A.K A.L p.1 * (1 - e) + algebraMap A.K A.L p.2 * e := by
    intro p
    simp only [Hyp.cc, star_add, star_mul, star_sub, star_one, hse, A.star_K]
    ring
  have hme : ∀ p : A.K × A.K, Hyp.cc A e p * e = algebraMap A.K A.L p.1 * e := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) * hee
  have hmf : ∀ p : A.K × A.K, Hyp.cc A e p * (1 - e) = algebraMap A.K A.L p.2 * (1 - e) := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.2 - algebraMap A.K A.L p.1) * hee
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [Hyp.ci]
    rw [hme p, hmf p, htrs, htrs, hte, htf, mul_one, mul_one]
  · intro y
    simp only [Hyp.cc, Hyp.ci, htr, star_mul, star_sub, star_one, hse]
    linear_combination (2 * y - 2 * star y) * hee
  · intro p
    apply hinj
    rw [hnorm, hst, map_mul]
    simp only [Hyp.cc]
    linear_combination (-(algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) ^ 2) * hee
  · intro ψ x p q
    have hprod : star (Hyp.cc A e q) * Hyp.cc A e p =
        algebraMap A.K A.L (q.1 * p.2) * (1 - e) + algebraMap A.K A.L (q.2 * p.1) * e := by
      rw [hst]
      simp only [Hyp.cc, map_mul]
      linear_combination
        (algebraMap A.K A.L q.1 * algebraMap A.K A.L p.2 + algebraMap A.K A.L q.2 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.1 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.2 * algebraMap A.K A.L p.2) * hee
    have ht : Algebra.trace A.K A.L (star (Hyp.cc A e q) * Hyp.cc A e p) = q.1 * p.2 + q.2 * p.1 := by
      rw [hprod, map_add (f := _), htrs, htrs, hte, htf, mul_one, mul_one]
    simp only [Et.kerL, Hyp.kx, Et.psiK]
    rw [ht]
    rw [show x * (q.1 * p.2 + q.2 * p.1) = x * q.1 * p.2 + x * q.2 * p.1 by ring, map_add (f := _),
      AddChar.map_add_eq_mul]
  · intro s p
    simp only [Hyp.cc, Algebra.smul_def, map_mul]
    ring
  · intro s
    have hs : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine isUnit_iff_exists_inv.mpr ⟨Hyp.cc A e (((s⁻¹ : A.Kˣ) : A.K), 1), ?_⟩
    simp only [Hyp.cc, map_one]
    linear_combination
      (2 - algebraMap A.K A.L (s : A.K) - algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K)) * hee + e * e * hs

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvr
section
namespace GlobalTheory.IntegralClosureFG

theorem integralClosure_fg (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  classical
  let b0 := Module.finBasis E A
  have hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i) := by
    intro i
    have h : IsAlgebraic E (b0 i) := Algebra.IsAlgebraic.isAlgebraic _
    have h' : IsAlgebraic O (b0 i) := (IsFractionRing.isAlgebraic_iff O E A).2 h
    obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
    exact ⟨d, hd, hi⟩
  choose d hd0 hdi using hex
  have hu : ∀ i, IsUnit (algebraMap O E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let D : E := (Algebra.traceMatrix E b).det
  have hD : D ≠ 0 := by
    have h1 := (GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A)
      (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent
    rwa [Algebra.discr_def] at h1
  have hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e := by
    intro e he
    exact IsIntegrallyClosed.isIntegral_iff.1 he
  let S : Submodule O A := Submodule.span O (Set.range fun j => D⁻¹ • b j)
  have hS : S.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S := by
    intro x hx
    have hx' : IsIntegral O x := hx
    obtain ⟨v, hv⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x
      (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        ((hb i).mul (hb j))))
      (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        (hx'.mul (hb i))))
    have hx2 : x = ∑ j, v j • (D⁻¹ • b j) := by
      have : x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      rw [this, hv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]
    rw [hx2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS
  exact isNoetherian_submodule.1 this _ hle

end GlobalTheory.IntegralClosureFG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Step.EmbClosed

theorem embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

theorem continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _

theorem isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)

theorem isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by
  have hE := isClosedEmbedding_embHom r F
  let Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ :=
    Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)
  have hΦ : IsClosedEmbedding Φ := by
    refine hE.prodMap ?_
    exact MulOpposite.opHomeomorph.isClosedEmbedding.comp
      (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _ := by
    funext g
    rfl
  rw [← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]
  exact hΦ.comp Units.isClosedEmbedding_embedProduct

end GlobalTheory.JR.Step.EmbClosed
end
end

