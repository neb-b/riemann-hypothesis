module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.QuadT

section Abstract

variable {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (u l : ι → κ → A)

theorem core_term (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (a b : ι) (i j k : κ) :
    u a k * l a i * (u b j * l b k) =
      u a k * l b k * (l a i * u b j) - if k = j then u a k * l a i else 0 := by
  have e1 : u b j * l b k = l b k * u b j - if k = j then 1 else 0 := by
    rw [h b k j]; abel
  have e2 : u a k * l a i * (l b k * u b j) = u a k * l b k * (l a i * u b j) := by
    calc _ = u a k * (l a i * l b k) * u b j := by simp only [mul_assoc]
      _ = u a k * (l b k * l a i) * u b j := by rw [hll]
      _ = _ := by simp only [mul_assoc]
  rw [e1, mul_sub, e2]
  split_ifs <;> simp

theorem core1 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (i j : κ) :
    ∑ k, (∑ a, u a k * l a i) * (∑ b, u b j * l b k) =
      (∑ a, ∑ b, (∑ k, u a k * l b k) * (l a i * u b j)) -
        (Fintype.card ι : ℂ) • ∑ a, u a j * l a i := by
  simp only [Finset.sum_mul, Finset.mul_sum, core_term u l h hll, Finset.sum_sub_distrib]
  congr 1
  · calc (∑ k, ∑ b, ∑ a, u a k * l b k * (l a i * u b j))
          = ∑ b, ∑ k, ∑ a, u a k * l b k * (l a i * u b j) := Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ k, u a k * l b k * (l a i * u b j) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

theorem core2 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0) (i j : κ) :
    ∑ a, l a i * u a j = ∑ a, u a j * l a i + if i = j then (Fintype.card ι : ℂ) • (1 : A) else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

end Abstract

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

section Main

variable {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (u l : ι → κ → Module.End ℂ V) (E : ι → ι → Module.End ℂ V) (G : κ → κ → Module.End ℂ V)

theorem quad_main (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c)
    (hE : ∀ a b, E a b = ∑ c, u a c * l b c + (if a = b then (Fintype.card κ : ℂ) / 2 else 0) • 1)
    (hG : ∀ c d, G c d = ∑ a, u a c * l a d + (if c = d then (Fintype.card ι : ℂ) / 2 else 0) • 1)
    (x : ℂ) (i j : κ) :
    qop (fun c d => -G d c) ((Fintype.card κ : ℂ) / 2 - x)
        ((Fintype.card ι : ℂ) ^ 2 / 4 + (x - (Fintype.card κ : ℂ) / 2) * (Fintype.card ι : ℂ) / 2) i j =
      ∑ a, ∑ b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) := by
  have hR : ∀ a b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) =
      (∑ c, u a c * l b c) * (l a i * u b j) +
        (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) := by
    intro a b
    rw [hE]
    split_ifs <;> simp [add_mul, sub_mul, sub_smul, smul_mul_assoc, add_sub_assoc]
  simp only [hR, Finset.sum_add_distrib]
  have hD : ∑ a, ∑ b, (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) =
      ((Fintype.card κ : ℂ) / 2 - x) • ∑ a, l a i * u a j := by
    simp [ite_smul, Finset.sum_ite_eq, Finset.smul_sum]
  have h1 := core1 u l h hll i j
  rw [eq_sub_iff_add_eq] at h1
  rw [hD, core2 u l h, ← h1]
  simp only [qop, hG]
  simp only [neg_mul_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Finset.sum_add_distrib, ite_smul, zero_smul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    module
  · simp only [hij, Ne.symm hij, if_false]
    module

end Main

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

theorem fockAct1_Eab_eq {P Q R S : ℕ} (a b : Ix P Q) :
    fockAct1 P Q R S (Eab a b) =
      ∑ c, raiB (a, c) * lowB (b, c) + (if a = b then (Fintype.card (Ix R S) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct1_Eab]
  simp only [omE, Prod.mk.injEq, and_true, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem fockAct2_Eab_eq {P Q R S : ℕ} (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) =
      ∑ a, raiB (a, c) * lowB (a, d) + (if c = d then (Fintype.card (Ix P Q) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct2_Eab]
  simp only [omE, Prod.mk.injEq, true_and, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem negT_fockAct2_quad : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f,
    qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  intro P Q R S x
  refine ⟨(Fintype.card (Ix R S) : ℂ) / 2 - x,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 + (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2,
    fun i j f => ?_⟩
  have key : qop (negT (units (fockAct2 P Q R S))) ((Fintype.card (Ix R S) : ℂ) / 2 - x)
      ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 +
        (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2) i j =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab a b) - (if a = b then x else 0) • 1) *
        (lowB (a, i) * raiB (b, j)) :=
    quad_main (fun (a : Ix P Q) (c : Ix R S) => raiB (a, c)) (fun a c => lowB (a, c))
      (fun a b => fockAct1 P Q R S (Eab a b)) (fun c d => fockAct2 P Q R S (Eab c d))
      (fun b c e => by simp [GlobalTheory.FockCasimir.lowB_mul_raiB])
      (fun a c b e => GlobalTheory.FockCasimir.lowB_comm _ _) fockAct1_Eab_eq fockAct2_Eab_eq x i j
  rw [key, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [Module.End.mul_apply]
  apply Submodule.subset_span
  refine ⟨Eab a b, (lowB (a, i) * raiB (b, j)) f, ?_⟩
  by_cases hab : a = b
  · subst hab
    simp [Eab, Matrix.trace_single_eq_same]
  · simp [hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

end GlobalTheory.HoweR.QuadT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCusp
section
noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem orbK_eq_twOrbU {G : Type} [Group G] (K0 : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K0 γ f =
      GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id G) γ ⊓ K0) f := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum
  refine finsum_congr fun q => ?_
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']
  simp only [MonoidHom.id_apply, GlobalTheory.LKCount.vol, GlobalTheory.LKLoc.volRat, GlobalTheory.LKLoc.locPart]
  congr 1
  push_cast
  rw [inv_div]

end GlobalTheory.OrbDesc

namespace GlobalTheory.LKCount

theorem orbK_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKCount.orbK (MonoidHom.id (GL ι K)) K0 γ f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 hK0o hK0c hbi
  rw [GlobalTheory.OrbDesc.orbK_eq_twOrbU K0 γ f hbi]
  exact GlobalTheory.OrbDesc.twOrbU_eq_zero_of_cusp K ι f hlc hcs hyp γ hsep hirr K0 K0 hK0o hK0c hK0o hK0c hbi

end GlobalTheory.LKCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralZeroOfDerivativeAlongConjCurve
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

open GlobalTheory.AutomorphicL2Unitary Set

namespace GlobalTheory.Orb

theorem orbInt_comp_conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (dh : Measure H)
    [dh.IsHaarMeasure] [dh.IsMulRightInvariant] (γ : H) (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (g : H) (f : H → ℂ) :
    orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  rw [orbInt, quotInt, h3]
  exact hr.integral_comp' _

theorem orbitalIntegral_zero_of_derivative_along_conj_curve {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H) (hs : IsProperOrbit (cent s) s) (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H) (hc : Continuous c) (f f' : H → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f') (hf'c : HasCompactSupport f') (hd : ∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) : HasOrbInt μ s dt f' 0 := by
  have hO := hs.hasOrbInt (dh := μ) (dt := dt) hf' hf'c
  refine ⟨hO.1, ?_⟩
  change orbInt μ s dt f' = 0
  set ν := quotMeas (cent s) dt μ
  have hcf : ∀ (φ : H → ℂ) (g : H), Continuous φ → Continuous (conjFn s (φ ∘ conjEquiv g)) := fun φ g hφ =>
    hφ.comp ((conjEquiv g).continuous.comp (by fun_prop : Continuous fun x : H => x⁻¹ * s * x))
  have hmeas : ∀ (φ : H → ℂ) (g : H), Continuous φ →
      AEStronglyMeasurable (descend (cent s) (conjFn s (φ ∘ conjEquiv g))) ν := fun φ g hφ =>
    (measurable_descend (leftInv_conjFn le_rfl _) (hcf φ g hφ).measurable).aestronglyMeasurable
  let F : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f ∘ conjEquiv (c v)⁻¹))
  let F' : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f' ∘ conjEquiv (c v)⁻¹))
  have hconst : ∀ v, ∫ q, F v q ∂ν = orbInt μ s dt f := fun v =>
    orbInt_comp_conjEquiv μ s dt (c v)⁻¹ f

  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hf'c
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set K : Set H := (fun p : ℝ × H => c p.1 * p.2 * (c p.1)⁻¹) '' (Icc (-1) 1 ×ˢ tsupport f')
  have hK : IsCompact K := (isCompact_Icc.prod hf'c).image (by fun_prop)
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let χC : H → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hχC : Continuous χC := by fun_prop
  have hχCc : HasCompactSupport χC := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hχc Complex.ofReal_zero
  have hχO := hs.hasOrbInt (dh := μ) (dt := dt) hχC hχCc
  let bound : Quot (cent s) → ℝ := fun q => M * ‖descend (cent s) (conjFn s χC) q‖
  have hbound : Integrable bound ν := hχO.1.norm.const_mul M
  have hb : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, ‖F' v q‖ ≤ bound q := by
    intro q v hv
    change ‖f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹)‖ ≤ M * ‖χC (q.out⁻¹ * s * q.out)‖
    rw [inv_inv]
    set y := (c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v
    by_cases hy : y ∈ tsupport f'
    · have hx : q.out⁻¹ * s * q.out ∈ K := ⟨(v, y), ⟨hv, hy⟩, by simp only [y]; group⟩
      have : χC (q.out⁻¹ * s * q.out) = 1 := by simp [χC, hχ1 hx]
      rw [this, norm_one, mul_one]
      exact hM y
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  have hderiv : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun w => F w q) (F' v q) v := by
    intro q v _
    have e1 : (fun w => F w q) = fun w => f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * c w) := funext fun w => by
      change f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * (c w)⁻¹⁻¹) = _
      rw [inv_inv]
    have e2 : F' v q = f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v) := by
      change f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹) = _
      rw [inv_inv]
    rw [e1, e2]
    exact hd _ v
  have hF0 : Integrable (F 0) ν :=
    (hs.hasOrbInt (dh := μ) (dt := dt) (f := f ∘ conjEquiv (c 0)⁻¹) (hf.comp (conjEquiv _).continuous)
      (hfc.comp_homeomorph (conjEquiv (c 0)⁻¹).toHomeomorph)).1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := bound) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun v => hmeas f _ hf) hF0 (hmeas f' _ hf')
    (ae_of_all _ hb) hbound (ae_of_all _ hderiv)
  have h0 : HasDerivAt (fun v => ∫ q, F v q ∂ν) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  have := h0.unique hmain.2
  rw [← orbInt_comp_conjEquiv μ s dt (c 0)⁻¹ f']
  exact this.symm

theorem hasOrbInt_zero_of_hasDerivAt_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsProperOrbit (cent s) s → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H), Continuous c → ∀ (f f' : H → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' → (∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) → HasOrbInt μ s dt f' 0 :=
  fun _ _ _ _ _ _ _ _ _ μ _ _ s hs dt _ _ c hc f f' hf hfc hf' hf'c hd =>
    orbitalIntegral_zero_of_derivative_along_conj_curve μ s hs dt c hc f f' hf hfc hf' hf'c hd

end GlobalTheory.Orb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.inner_EEp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH hPos hB p q hpq e he e' he'

  have hmap : ∀ r, (R.EEp3 r).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
      Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum r.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) := by
    intro r
    rw [Submodule.map_le_iff_le_comap]
    exact iSup₂_le fun c hc => Submodule.map_le_iff_le_comap.1 hc.2
  have hx : LinearMap.adjoint (R.Th A3.A.μ0) e ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap p (Submodule.mem_map_of_mem he)
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) e' ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap q (Submodule.mem_map_of_mem he')
  have h0 := _root_.GlobalTheory.Div.parts_orth_complex R F hOk hC hH p q hpq _ hx _ hy
  have hk := hB A3.A.μ0 p e he
  rw [LinearMap.comp_apply] at hk
  have hin : ⟪R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) e), e'⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right]; exact h0
  rw [hk, inner_smul_left] at hin
  have ha : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    rw [RealDat3.prod_lamN]
    exact mul_pos hPos.1 (Finset.prod_pos fun j _ => hPos.2 j _ _)
  rcases mul_eq_zero.1 hin with h | h
  · exfalso
    rw [Complex.conj_ofReal] at h
    exact ha.ne' (by exact_mod_cast h)
  · exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentSmulMemCompletedSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.IdemLat

theorem finPart_idem_mem {D : D7} {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D}
    (h : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    finPart D e ∈ intAE D := by
  have h1 : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h1 =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := not_not.1 fun hn => h1 ((h 1 one_ne_zero).2 hn)
  simpa using this

theorem finPart_placeIdem_mem {D : D7} {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) : finPart D f ∈ intAE D := by
  rcases h with ⟨⟨_, h⟩, rfl⟩ | ⟨rfl, _, h⟩
  · have he := finPart_idem_mem h
    rw [RingHom.map_add (f := _)]
    exact add_mem he (GlobalTheory.IdemSupport.finPart_cA_mem he)
  · exact finPart_idem_mem h

theorem lamHat_idem : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f →
    ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V := by
  intro D V P e f h y hy
  exact (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _ (finPart_placeIdem_mem h) y hy

end GlobalTheory.IdemLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenterStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powers_linearIndependent_over_localTensorCenter : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F), ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  first | (exact @GlobalTheory.OrbFinAf.pow_indep_tensor) | (exact GlobalTheory.OrbFinAf.pow_indep_tensor) | (intros; apply GlobalTheory.OrbFinAf.pow_indep_tensor  <;> assumption)
end

