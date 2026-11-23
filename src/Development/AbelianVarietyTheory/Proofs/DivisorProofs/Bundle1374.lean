module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerIffIntegralUnitsOfModel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, ψ (a * y) = M *ᵥ ψ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun ψ
  let φ : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective φ := Algebra.leftMulMatrix_injective b
  have hφ : φ a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hφ]
  exact (isIntegral_algHom_iff φ hinj).symm

theorem cptPart_iff_intUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e he hint n B ψ x γ hmod hsep τ hτ t
  have hcont := (GlobalTheory.ConjAtPlace.main E hE w).1
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    unfold UL; rw [if_neg hw]
    have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
        (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
          (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
    rw [this]
    refine IsClosed.preimage ?_ isClosed_singleton
    unfold cT
    exact (((Units.continuous_val.matrix_map hcont).matrix_transpose).matrix_mul continuous_const).matrix_mul
      Units.continuous_val
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  have key : ∀ s : twCent (MonoidHom.id (UL n w)) γ,
      IsCompact (closure (Subgroup.zpowers (s : UL n w) : Set (UL n w))) ↔ (τ s : B.Aˣ) ∈ intUnits K.O B.A := by
    intro s
    have hinv : ((τ s : B.Aˣ))⁻¹ = ((τ s⁻¹ : B.T) : B.Aˣ) := by rw [map_inv, Subgroup.coe_inv]
    have hI1 : IsIntegral K.O ((τ s : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B ψ _ _ (hτ s), _root_.GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((τ s : B.Aˣ))⁻¹ : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [hinv, isIntegral_iff_of_mulVec B ψ _ _ (hτ s⁻¹), _root_.GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat, Subgroup.coe_inv]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl (s : UL n w)]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  let H' : Subgroup (UL n w) := ((intUnits K.O B.A).comap (B.T.subtype.comp τ.toMonoidHom)).map
    (twCent (MonoidHom.id (UL n w)) γ).subtype
  constructor
  · intro ht
    have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro u ⟨hu, hc⟩
      exact ⟨⟨u, hu⟩, (key ⟨u, hu⟩).1 hc, rfl⟩
    obtain ⟨t₀, ht₀, he₀⟩ := hle ht
    have : t₀ = t := Subtype.ext he₀
    subst this
    exact ht₀
  · intro ht
    exact Subgroup.subset_closure ⟨t.2, (key t).2 ht⟩

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

end Lin

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
  {C : GL (Fin n) E} {l d : ℕ}


end Frame

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]


theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2



variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

end Adele


end GlobalTheory.BlockForms.LeviLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineTheta
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaLineSmoothF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Form

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)

theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ (x + x') y = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ x (y + y') = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_zero_right (y : WOF F E nS nT) : symplOHF σ JS JT ξ y 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ y 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT ξ 0 y = 0 := by
  have := symplOHF_add_left σ JS JT ξ 0 0 y
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem sum_reorder {A : Type} [CommRing A] {m n : ℕ} (c : A → A) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (x y : Matrix (Fin n) (Fin m) A) :
    ∑ a, ∑ b, ∑ c', ∑ d, P a b * c (y c' b) * Q c' d * x d a =
      ∑ i, ∑ j, ∑ k, ∑ l, c (yᵀ i j) * P k i * Q j l * xᵀ k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Matrix.transpose_apply]; ring

theorem snd_symplOHF (x y : WOF F E nS nT) (h : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ x y) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : sndA F (symplOF σ JS JT ξ x y) = 0 := by
    unfold symplOF hOF
    rw [sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero (sndA F) σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (Or.inr ?_)
    ext i j
    exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem continuous_symplOHF {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ (x t) (y t) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hconj : Continuous (cAF σ : AEF F E → AEF F E) := by
    refine IsModuleTopology.continuous_of_ringHom (R := AF F) (cAF σ) ?_
    have h : (cAF σ).comp (algebraMap (AF F) (AF F ⊗[F] E)) = algebraMap (AF F) (AF F ⊗[F] E) := by
      ext a
      show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E)
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rw [h]
    exact continuous_algebraMap _ _
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    hconj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hOF σ JS JT (x t) (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

end Form

theorem exists_log {ψ : AddChar (AF F) ℂ} {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by
        simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

theorem contDiff_deriv_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)

end GlobalTheory.ThetaLineSmoothF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnChernFormOfGramMatrixAtCoefficients
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernSmooth

section General

variable {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing B] [Algebra ℂ B]

def WeakSmooth (s : Set E) (F : E → B) : Prop := ∀ φ : B →ₗ[ℂ] ℂ, ContDiffOn ℝ ∞ (fun v => φ (F v)) s

def mult (B : Type) [CommRing B] [Algebra ℂ B] (s : Set E) : Subring (E → B) where
  carrier := {G | ∀ F, WeakSmooth s F → WeakSmooth s (G * F)}
  mul_mem' {a b} ha hb F hF := by rw [mul_assoc]; exact ha _ (hb _ hF)
  one_mem' F hF := by rwa [one_mul]
  add_mem' {a b} ha hb F hF φ := by
    simpa [add_mul] using (ha F hF φ).add (hb F hF φ)
  zero_mem' F hF φ := by simpa using contDiffOn_const
  neg_mem' {a} ha F hF φ := by simpa using (ha F hF φ).neg

theorem smul_mem {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f s) (b : B) : (fun v => f v • b) ∈ mult B s := by
  intro F hF φ
  simpa using hf.mul (hF (φ ∘ₗ LinearMap.mulLeft ℂ b))

theorem const_mem (s : Set E) (b : B) : (fun _ => b) ∈ mult B s := by
  simpa using smul_mem (s := s) (f := fun _ => (1 : ℂ)) contDiffOn_const b

theorem weakSmooth_of_mem {s : Set E} {G : E → B} (h : G ∈ mult B s) : WeakSmooth s G := by
  simpa using h 1 fun φ => by simpa using contDiffOn_const

theorem det_mem {s : Set E} {r : Type} [Fintype r] [DecidableEq r] {M : E → Matrix r r B}
    (h : ∀ i j, (fun v => M v i j) ∈ mult B s) : (fun v => (M v).det) ∈ mult B s := by
  have : (fun v => (M v).det) = ∑ σ : Equiv.Perm r, ((Equiv.Perm.sign σ : ℤ) : E → B) * ∏ i, fun v => M v (σ i) i := by
    funext v
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

end General

theorem contDiffOn_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  intro n r _ _ H s hs hH hu j S
  have hc : ∀ ξ η a b, ContDiffOn ℝ ∞ (fun v => curv H v ξ η a b) s := fun ξ η a b v hv =>
    (MContDiffAt.curv (k := ∞) (j := ∞) (fun a b => (hH a b).contDiffAt (hs.mem_nhds hv)) (hu v hv)
      (by norm_cast) ξ η a b).contDiffWithinAt
  have hd : (fun v => (-curvPoly H v).charpolyRev) ∈ mult (Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) s := by
    unfold Matrix.charpolyRev
    refine det_mem fun a b => ?_
    have : (fun v => (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
        (-curvPoly H v).map Polynomial.C) a b) = (fun _ => (1 : Matrix r r _) a b) + ∑ c, ∑ d, fun v =>
          curv H v (coordVec c) (coordVec d) a b • (Polynomial.X * Polynomial.C (MvPolynomial.X (c, d))) := by
      funext v
      simp [curvPoly, Finset.sum_apply, Finset.mul_sum, MvPolynomial.C_mul', ← Polynomial.smul_C]
    rw [this]
    exact add_mem (const_mem _ _) (sum_mem fun c _ => sum_mem fun d _ => smul_mem (hc _ _ _ _) _)
  let φ : Polynomial (MvPolynomial (Fin n × Fin n) ℂ) →ₗ[ℂ] ℂ :=
    (bas n).coord S ∘ₗ (Subalgebra.center ℂ (Alt n)).val.toLinearMap ∘ₗ (kappa ^ j • (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toLinearMap) ∘ₗ
      (Polynomial.lcoeff _ j).restrictScalars ℂ
  exact weakSmooth_of_mem hd φ

end GlobalTheory.ChernSmooth
end
end

