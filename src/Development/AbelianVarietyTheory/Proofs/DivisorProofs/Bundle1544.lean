module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0100
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansion
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchTrigBump

theorem exists_bounded_trig {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type} [AddCommGroup B]
    (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b)) (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (hzero : ∀ x, χ 0 x = 1) (hnorm : ∀ a x, ‖χ a x‖ = 1) (hsep : ∀ x y, x ≠ y → ∃ b, χ b x ≠ χ b y)
    (β : X → ℝ) (hβ : Continuous β) (h01 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ), (∀ n x, ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * χ b x) Filter.atTop (nhds (β x : ℂ)) := by
  first
  | exact @_root_.GlobalTheory.RealAlgebraCharacters.main
  | exact _root_.GlobalTheory.RealAlgebraCharacters.main
  | (apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealAlgebraCharacters.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealAlgebraCharacters.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealAlgebraCharacters.main ..)

variable {F : Type} [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


open scoped Classical in
theorem exists_trace_mul_ne_zero (u : mixedEmbedding.mixedSpace F) (hu : u ≠ 0) :
    ∃ w, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u * w) ≠ 0 := by
  let w : mixedEmbedding.mixedSpace F := (fun v => (u.1 v)⁻¹, fun v => (u.2 v)⁻¹)
  have h1 : u * w * u = u := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · change u.1 v * (u.1 v)⁻¹ * u.1 v = u.1 v
      exact mul_inv_mul_cancel _
    · change u.2 v * (u.2 v)⁻¹ * u.2 v = u.2 v
      exact mul_inv_mul_cancel _
  have h2 : IsIdempotentElem (u * w) := by
    change u * w * (u * w) = u * w
    rw [← mul_assoc, h1]
  refine ⟨w, fun h => hu ?_⟩
  rw [Algebra.trace_apply] at h
  have h3 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff
    (h2.map (Algebra.lmul ℝ (mixedEmbedding.mixedSpace F)))).1 h
  have h4 := LinearMap.congr_fun h3 u
  simp only [LinearMap.zero_apply] at h4
  rw [← h1]
  exact h4


open scoped Classical in
theorem exists_char_ne {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) (hxy : x ≠ y) :
    ∃ w : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ w) : ℝ)) ≠
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ w) : ℝ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  obtain ⟨w, hw⟩ := exists_trace_mul_ne_zero (x i - y i) (sub_ne_zero.2 hi)
  set t := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((x i - y i) * w) with ht
  refine ⟨Pi.single i ((2 * t)⁻¹ • w), fun h => ?_⟩
  rw [dotProduct_single, dotProduct_single] at h
  have h1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y i * ((2 * t)⁻¹ • w)) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) - 1 / 2 := by
    have : (2 * t)⁻¹ * t = 1 / 2 := by field_simp
    rw [← this, mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    congr 1
    rw [ht, sub_mul, map_sub]
    ring
  rw [h1] at h
  generalize Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x i * ((2 * t)⁻¹ • w)) = a at h
  have h2 : -(2 * Real.pi * Complex.I) * ((a - 1 / 2 : ℝ) : ℂ) =
      -(2 * Real.pi * Complex.I) * (a : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I] at h
  have h3 := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (a : ℂ))
  apply h3
  linear_combination h / 2

theorem arch_bump_trig : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  intro F _ _ κ _ ψ hψ U y hU hy
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let P : (κ → Ainf F) → κ → mixedEmbedding.mixedSpace F := fun u i => e (u i)
  let Q : (κ → mixedEmbedding.mixedSpace F) → κ → Ainf F := fun u i => e.symm (u i)
  have hP : Continuous P := continuous_pi fun i => continuous_toMixed.comp (continuous_apply i)
  have hQ : Continuous Q := continuous_pi fun i => continuous_ofMixed.comp (continuous_apply i)
  have hQP : ∀ u, Q (P u) = u := fun u => funext fun i => e.symm_apply_apply _
  have hU' : IsClosed (Q ⁻¹' U)ᶜ := (hU.preimage hQ).isClosed_compl
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hU'
    (isClosed_singleton (x := P fun i => (y i).1))
    (Set.disjoint_singleton_right.2 fun h => h (by rw [Set.mem_preimage, hQP]; exact hy))
  let χ : (κ → mixedEmbedding.mixedSpace F) → (κ → mixedEmbedding.mixedSpace F) → ℂ := fun w u =>
    Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ w) : ℝ))
  have hT : Continuous (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨s, c, hb, hl⟩ := exists_bounded_trig 0 χ
    (fun w => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hT.comp (continuous_id.dotProduct continuous_const)))))
    (fun a b x => by simp only [χ, dotProduct_add, map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add])
    (fun x => by simp [χ])
    (fun a x => by simp [χ, Complex.norm_exp])
    exists_char_ne f f.continuous (fun u => hf u)
  let ι : (κ → mixedEmbedding.mixedSpace F) → κ → AF F := fun w i => ((e.symm (w i), 0) : Ainf F × Af F)
  let ρ : (κ → AF F) → κ → mixedEmbedding.mixedSpace F := fun b i => e (b i).1
  have hρ : ∀ w, ρ (ι w) = w := fun w => funext fun i => e.apply_symm_apply _
  have hι : Function.Injective ι := Function.LeftInverse.injective hρ
  have hchar : ∀ (x : κ → AF F) w, ψ (x ⬝ᵥ ι w) = χ w (P fun i => (x i).1) := by
    intro x w
    have h2 : (x ⬝ᵥ ι w).2 = 0 := by
      have := map_sum (RingHom.snd (Ainf F) (Af F)) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_eq_zero fun i _ => ?_)
      exact mul_zero (x i).2
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x ⬝ᵥ ι w) = (P fun i => (x i).1) ⬝ᵥ w := by
      have := map_sum (e.toRingHom.comp (RingHom.fst (Ainf F) (Af F))) (fun i => x i * ι w i) Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      change e ((x i).1 * e.symm (w i)) = _
      rw [map_mul, e.apply_symm_apply]
    rw [hψ.2.2, h1]
    intro u hu
    have hu1 : u.1 = 0 := e.injective (hu.trans (map_zero e).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * (x ⬝ᵥ ι w).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (x ⬝ᵥ ι w).2 = 0
      rw [h2, mul_zero]
  have hsum : ∀ n (x : κ → AF F), ∑ b ∈ (s n).map ⟨ι, hι⟩, c n (ρ b) * ψ (x ⬝ᵥ b) =
      ∑ w ∈ s n, c n w * χ w (P fun i => (x i).1) := by
    intro n x
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Function.Embedding.coeFn_mk, hρ, hchar]
  refine ⟨fun u => f (P u), f.continuous.comp hP, fun u => hf _, hf1 rfl, fun u hu => ?_,
    fun n => (s n).map ⟨ι, hι⟩, fun n b => c n (ρ b), 2, ?_, fun n x => ?_, fun x => ?_⟩
  · by_contra h
    exact hu (hf0 (fun h' => h (by rwa [Set.mem_preimage, hQP] at h')))
  · intro n b hb v
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hb
    funext i
    refine Prod.ext ?_ ?_
    · exact zero_mul (e.symm (w i))
    · exact mul_zero (GlobalTheory.LatVac.liftV v 1).2
  · rw [hsum]; exact hb _ _
  · simp only [hsum]; exact hl _

end GlobalTheory.ArchTrigBump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaBoundVp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp c_vp delta_vp a0 n_vp IsClassZetaVals)
open GlobalTheory.CMVal (OF IsBaseCond expIn)

namespace GlobalTheory.DenExist

section Field

variable {E : Type} [Field E] [NumberField E]

theorem finite_support (d s : ℕ) {I : Type} [Fintype I] (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : 𝔣 ≠ ⊥)
    (z : ClassGroup (OF E) → ℚ) :
    {l : ℕ | l.Prime ∧ (⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) ≠ 0}.Finite := by
  set A : Set ℕ := {l | l.Prime ∧ ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal} with hAdef
  have hA : A.Finite :=
    GlobalTheory.FunObj.SqNum.finite_primes_under (K := maximalRealSubfield E) (p := fun v => v.asIdeal ∣ 𝔣)
      (Ideal.finite_factors h𝔣)
  let B : Finset ℕ := (Finset.univ.biUnion fun C =>
    (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)).den.primeFactors) ∪ (discr E).natAbs.primeFactors
  refine (hA.union B.finite_toSet).subset ?_
  rintro l ⟨hl, hn⟩
  by_contra hc
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hc
  obtain ⟨hlA, hlB⟩ := hc
  apply hn
  have hv : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → ¬ v.asIdeal ∣ 𝔣 :=
    fun v h1 h2 => hlA ⟨hl, v, h2, h1⟩
  have ha0 : a0 𝔣 l = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro _ ⟨v, h1, rfl⟩
    simp [expIn, multiplicity_eq_zero_of_not_dvd (hv v h1)]
  have hcv : c_vp 𝔣 l = 0 := by
    have hd : ¬ l ∣ (discr E).natAbs := fun h => hlB (Finset.mem_union_right _
      (Nat.mem_primeFactors.2 ⟨hl, h, by simpa using discr_ne_zero E⟩))
    rw [c_vp, if_neg (fun ⟨v, h1, h2⟩ => hv v h1 h2), delta_vp]
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hd]
  have hcE : cE_vp l z = 0 := by
    rw [cE_vp, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    intro C _
    set q := z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)
    have hd : ¬ l ∣ q.den := fun h => hlB (Finset.mem_union_left _ (Finset.mem_biUnion.2
      ⟨C, Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hl, h, q.den_ne_zero⟩⟩))
    show (-padicValRat l q).toNat = 0
    rw [Int.toNat_eq_zero, padicValRat, padicValNat.eq_zero_of_not_dvd hd]
    simp
  simp [betaBound_vp, hcE, hcv, ha0, n_vp]

end Field

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem exists_denom (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hb : IsBaseCond (condF G.pl)) (i j : Fin D.R.m) (s : ℕ) (hs : 1 ≤ s) :
    ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
  obtain ⟨⟨z, hz'⟩, -⟩ := @hz D.host.E _ _ hcm s hs
  refine ⟨fun l => ((⌈betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ) : ℝ),
    ⟨z, hz', fun l _ => rfl⟩, ?_⟩
  refine (finite_support D.host.d s (kap D sc.cGap i j s) (condF G.pl) hb.1 z).subset ?_
  rintro l ⟨hl, h⟩
  exact ⟨hl, fun h' => h (by simp only [h', Nat.cast_zero])⟩

theorem denEx (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hF : FieldDat) : DenEx := by
  obtain ⟨CF0, h⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, -, -, hb, -⟩ := h C hC D large₂ he hx hR T Lc μ₀ hL G
  exact fun i j s hs _ => exists_denom hz G hcm hb i j s hs

end GlobalTheory.DenExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRouteIdent

open GlobalTheory.RouteSeesaw

theorem kerBig_norm_le_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hd := _root_.GlobalTheory.RouteSeesaw.isThetaFunO_of_isMatched hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, χa, χb, hω₂, hadj⟩ := _root_.GlobalTheory.AdjSwap.weil_adjoint_negSource W.ψ W.ψ_std _ _ _ _ _ h2
  obtain ⟨ω', χ, χ', c, hω', hc, hbox⟩ := GlobalTheory.SeesawSumTarget.seesaw_sum W.ψ W.ψ_std _ _ _ _ _ _ _ _ ω₂ h1 hω₂
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  let Φ : WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ :=
    Θ.sum fun d a => a • box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))
  have hth : ∀ d ∈ Θ.support, IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs)
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) := fun d hdm =>
    (hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).1
  have e : ∀ u g, ∀ d ∈ Θ.support, thetaKO ω' (negGA S u) (GlobalTheory.SquareComm.blk A Bs (g, g₁))
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) =
      c (negGA S u) g g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁) := fun u g d hdm => by
    rw [(hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).2, (hadj _ (hd d hdm).2).2]
    rfl
  refine ⟨true, ω'.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)), χ, χ', Φ, 1, hω', ?_, ?_⟩
  · let U : Submodule ℂ (WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ) :=
      { carrier := {g | IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) g}
        add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
        zero_mem' := GlobalTheory.OrientedHeis.theta_zero
        smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
    show Φ ∈ U
    exact U.sum_mem fun d hdm => U.smul_mem _ (hth d hdm)
  · intro g u
    have key : ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0 = c (negGA S u) g g₁ * kerBig W Θ g g₁ u := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Φ, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hdm => ?_
      have := e u g d hdm
      simp only [thetaKO] at this
      rw [this]; ring
    refine le_of_eq ?_
    show ‖kerBig W Θ g g₁ u‖ = 1 * ‖ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0‖
    rw [key, norm_mul, hc, one_mul, one_mul]

end GlobalTheory.BigRouteIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {D : D7} {a a' : ℕ}

def coBar (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) :=
  -((1 : GL (Fin a') (Fv D.host.F Bs.v₁)).1ᵀ * Γ.V'.J.map Bs.τ₁ * u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) *
    (Γ.W.J.map Bs.τ₁)ᵀ * (1 : GL (Fin (a + a')) (Fv D.host.F Bs.v₁)).1)

theorem coBar_add (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u u' : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    coBar Bs Γ (u + u') = coBar Bs Γ u + coBar Bs Γ u' := by
  unfold coBar
  rw [Matrix.map_add _ (map_add _)]
  simp only [Matrix.mul_add, Matrix.add_mul, neg_add]

theorem coBar_zero (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') : coBar Bs Γ 0 = 0 := by
  unfold coBar
  rw [Matrix.map_zero _ (map_zero _)]
  simp

def Sa (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) :
    AddSubgroup (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) where
  carrier := {Y | ∃ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, u.map (piW Bs.τ₁) = 0 ∧ coBar Bs Γ u = Y}
  zero_mem' := ⟨0, zero_mem _, Matrix.map_zero _ (map_zero _), coBar_zero Bs Γ⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    exact ⟨u + u', add_mem hu hu', by rw [Matrix.map_add _ (map_add _), hu0, hu0', add_zero], coBar_add Bs Γ u u'⟩
  neg_mem' := by
    rintro _ ⟨u, hu, hu0, rfl⟩
    refine ⟨-u, neg_mem hu, by rw [Matrix.map_neg _ (map_neg _), hu0, neg_zero], ?_⟩
    have := coBar_add Bs Γ u (-u)
    rw [add_neg_cancel, coBar_zero] at this
    show coBar Bs Γ (-u) = -coBar Bs Γ u
    exact (neg_eq_of_add_eq_zero_right this.symm).symm

def Bd (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :=
  {Y | ∀ x : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E), At (evFin D.host.F Bs.v₁) x →
    x.map (piW Bs.τ₁) = 0 → coBar Bs Γ x = Y → ∀ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x u) = 1}

end GlobalTheory.VacShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractional
section
open NumberField

namespace GlobalTheory.ColonPowCancel

theorem exists_inv {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) : ∃ 𝔠 : Submodule (𝓞 K) K, 𝔠 * 𝔟 = 1 := by
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨𝔟, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply h0
    have : (I : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by rw [h]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  refine ⟨((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K), ?_⟩
  have h1 : I⁻¹ * I = 1 := inv_mul_cancel₀ hI
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h1
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at h2
  exact h2

theorem mem_colon_iff {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (N A : Submodule R K) (r : R) :
    r ∈ N.colon (A : Set K) ↔ Submodule.span R {algebraMap R K r} * A ≤ N := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    rw [Submodule.mul_le]
    intro m hm a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc, ← Algebra.smul_def]
    exact N.smul_mem c (h a ha)
  · intro h a ha
    rw [Algebra.smul_def]
    exact h (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) ha)

theorem colon_pow_mul_cancel {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) (p : ℕ) (A N : Submodule (𝓞 K) K) :
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  obtain ⟨𝔠, hc⟩ := exists_inv 𝔟 hfg h0
  have hp : 𝔠 ^ p * 𝔟 ^ p = 1 := by rw [← mul_pow, hc, one_pow]
  ext r
  rw [mem_colon_iff, mem_colon_iff, mul_left_comm]
  constructor
  · intro h
    have h' : 𝔠 ^ p * (𝔟 ^ p * (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r} * A))
        ≤ 𝔠 ^ p * (𝔟 ^ p * N) := by gcongr
    rwa [← mul_assoc, ← mul_assoc (𝔠 ^ p), hp, one_mul, one_mul] at h'
  · intro h
    gcongr

end GlobalTheory.ColonPowCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverSkewHermitianAdelicMatricesShrunkCompactStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  first | exact @GlobalTheory.SkewAdCover.cover | exact GlobalTheory.SkewAdCover.cover | (intros; apply GlobalTheory.SkewAdCover.cover <;> assumption)
end

