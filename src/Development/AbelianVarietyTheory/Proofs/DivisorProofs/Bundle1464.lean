module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateProperness

theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ p _ _ G _ hG g hg m hm s hs hcard
  classical
  obtain ⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  obtain ⟨g', hg', hiso⟩ := hdim g hg
  obtain ⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩ :=
    GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'

  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hcop : m.Coprime p := by
    have hnd : ¬ p ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)

  have hmono : Mono ν.left := inferInstance
  have hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y' := by
    intro y y' h
    ext1
    exact (cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)

  have hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x m hcop hm0 (hs x hx)
    refine ⟨y, hy, hinj _ _ ?_⟩
    rw [MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]
  choose! f hf1 hf2 using hlift'
  have hfinj : Set.InjOn f s := by
    intro x hx x' hx' h
    rw [← hf1 x hx, ← hf1 x' hx', h]
  have hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
    refine _root_.GlobalTheory.TorusExtTorsion.card_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf2 x hx
  rw [Finset.card_image_of_injOn hfinj] at hcardN

  have hpt : Nonempty (𝟙_ (Over (Sp k))).left := by
    change Nonempty (Sp k)
    first
    | infer_instance
    | exact ⟨IsLocalRing.closedPoint k⟩
  have hne : Nonempty N.left := ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩
  have hgle : g' ≤ g := _root_.GlobalTheory.relDim_le_of_isClosedImmersion k N G ν hνci hne g g' hg hg'

  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have : m = 1 := by omega
      subst this
      simp at hcard hcardN
      omega
  have hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1) := by
    calc m ^ (2 * g) < m * s.card := hcard
      _ ≤ m * m ^ (Module.finrank ℤ X + 2 * a) := Nat.mul_le_mul_left m hcardN
      _ = m ^ (Module.finrank ℤ X + 2 * a + 1) := by ring
  have hexp := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have ht : Module.finrank ℤ X = 0 := by omega
  have hgg : g ≤ g' := by omega
  haveI hP : IsProper N.hom := _root_.GlobalTheory.SS.isProper_of_isQuot_of_finrank_eq_zero k N X B i q hq hB ht
  haveI : IsIso ν.left := by
    haveI := hiso hgg
    exact Functor.map_isIso (Over.forget (Sp k)) ν
  have hw : G.hom = inv ν.left ≫ N.hom := by
    rw [← Over.w ν]
    simp
  rw [hw]
  infer_instance

end GlobalTheory.SerreTateProperness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DblTargetThetaF

open GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun := topR
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun x := -botR x
  map_zero' := by ext; simp [botR]
  map_add' x y := by ext; simp [botR]; ring

theorem continuous_topH (nS nT : ℕ) : Continuous (topH F E nS nT) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ j

theorem continuous_sndH (nS nT : ℕ) : Continuous (sndH F E nS nT) := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact (continuous_matrix fun i j => continuous_id.matrix_elem (finSumFinEquiv (Sum.inr i)) j).neg

theorem map_topH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (topH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j

theorem map_sndH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (sndH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u (finSumFinEquiv (Sum.inr i)) j) = 0 := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) j
    change φ (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
    rw [map_neg, e, neg_zero]

theorem hOF_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp [hOF]

theorem hOF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topH F E nS nT x) (topH F E nS nT y) -
      hOF σ JS JT (sndH F E nS nT x) (sndH F E nS nT y) := by
  change _ = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (-botR x) (-botR y)
  rw [hOF_neg]
  unfold hOF
  have hs : ∀ g : Fin (nT + nT) → AEF F E, ∑ a, g a =
      ∑ a, g (finSumFinEquiv (Sum.inl a)) + ∑ a, g (finSumFinEquiv (Sum.inr a)) := fun g => by
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hs]
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, dblG, GlobalTheory.WeilM.dbl, topH, topR, botR,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem symplOHF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topH F E nS nT x) (topH F E nS nT y) -
      symplOHF σ JS JT ξ₀ (sndH F E nS nT x) (sndH F E nS nT y) := by
  unfold symplOHF symplOF
  rw [hOF_dbl, mul_sub, map_sub, mul_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem deltaT_eq {nS nT : ℕ} (f₁ f₂ : WOF F E nS nT → ℂ) :
    deltaT f₁ f₂ = fun w => f₁ (topH F E nS nT w) * conj (f₂ (sndH F E nS nT w)) := rfl

theorem topH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    topH F E nS nT (ratWF γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl

theorem sndH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    sndH F E nS nT (ratWF γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
  ext i j
  change -((incAF F E) (γ _ j)) = (incAF F E) (-(γ _ j))
  rw [map_neg]

theorem isThetaFunOF_deltaT (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1)
    {f₁ f₂ : WOF F E nS nT → ℂ} (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  rw [deltaT_eq]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · rw [map_add (f := _), map_add (f := _), symplOHF_dbl, topH_ratWF, sndH_ratWF, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn,
      neg_neg, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (topH F E nS nT) ⊓ U₂.comap (sndH F E nS nT),
      (hU₁.preimage (continuous_topH nS nT)).inter (hU₂.preimage (continuous_sndH nS nT)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_topH _ h0)) (topH F E nS nT w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ h0)) (sndH F E nS nT w)
    simp only [heisOF] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOHF_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _), map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_topH nS nT)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH nS nT)))
  · simp only [map_add (f := _)]
    exact (h₁.smooth k ((topH F E nS nT).comp L) ((continuous_topH nS nT).comp hL) (fun t => map_topH _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH F E nS nT).comp L) ((continuous_sndH nS nT).comp hL)
        (fun t => map_sndH _ (h0 t)) _))

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
          (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ f₁ f₂ h₁ h₂
  exact isThetaFunOF_deltaT σ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1 h₁ h₂

end GlobalTheory.DblTargetThetaF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCount
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem model_mul_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w), IsModel w e B u x γ → ∀ c : B.Aˣ, IsModel w e B u (x * ((c : B.A) * B.σ (c : B.A))) γ := by
  intro E _ _ _ w K e B u x n γ hM c
  obtain ⟨ψ, h1, h2, h3⟩ := hM
  let φ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    { toFun := fun y => ψ ((c : B.A) * y)
      invFun := fun v => ((c⁻¹ : B.Aˣ) : B.A) * ψ.symm v
      left_inv := fun y => by simp [← mul_assoc]
      right_inv := fun v => by simp [← mul_assoc]
      map_add' := fun y z => by simp [mul_add] }
  refine ⟨φ, fun a y => ?_, fun y => ?_, fun y z => ?_⟩
  · show ψ ((c : B.A) * (a • y)) = e a • ψ ((c : B.A) * y)
    rw [mul_smul_comm, h1]
  · show ψ ((c : B.A) * (u * y)) = γ.val *ᵥ ψ ((c : B.A) * y)
    rw [show (c : B.A) * (u * y) = u * ((c : B.A) * y) by ring, h2]
  · show stdH w (ψ ((c : B.A) * y)) (ψ ((c : B.A) * z)) = _
    rw [h3]
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 2
    rw [map_mul]
    ring

theorem kapOrb_eq_kapSum_of_fits {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w)
    {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hBr : Bridge w K e) {k : ℕ} {t : K.O} (ht : K.Small t)
    (htk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) {n : ℕ} {Q₁ Q₂ : (w.adicCompletion E)[X]}
    {B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K} {u₁ : B₁.A} {u₂ : B₂.A} (hsep : (Q₁ * Q₂).Separable) (hmon : (Q₁ * Q₂).Monic)
    (hdeg : (Q₁ * Q₂).natDegree = n) (hF₁ : Fits w e B₁ Q₁ u₁) (hF₂ : Fits w e B₂ Q₂ u₂)
    (hg : 1 + algebraMap K.O (B₁.prod B₂).A t * (B₁.prod B₂).g = (u₁, u₂)) :
    kapOrb n w Q₁ Q₂ (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) =
      ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  have hcl : Equivalence (fun x y : {x : (B₁.prod B₂).Aˣ // (B₁.prod B₂).σ (x : (B₁.prod B₂).A) = x} =>
      ∃ u : (B₁.prod B₂).Aˣ, (y.1 : (B₁.prod B₂).A) = x.1 * (u * (B₁.prod B₂).σ (u : (B₁.prod B₂).A))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one, one_mul]
      rw [hu]
      calc (x.1 : (B₁.prod B₂).A) = x.1 * (((u : (B₁.prod B₂).A) * ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) *
          ((B₁.prod B₂).σ (u : (B₁.prod B₂).A) * (B₁.prod B₂).σ ((u⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) := by rw [h1, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩
  have hconj : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨g, rfl⟩; exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩; exact ⟨g * h, by simp [mul_assoc]⟩
  have hF := _root_.GlobalTheory.KapLat.fits_prod E w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂
  unfold kapOrb clSum GlobalTheory.UnitLemma.InvAlg.kapSum
  rw [cast_finsum]
  set S' : Set (TwCl (MonoidHom.id (UL n w))) := {c | c.rep.1.val.charpoly = Q₁ * Q₂} with hS'
  have hex : ∀ c : TwCl (MonoidHom.id (UL n w)), c ∈ S' → ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧
      IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 := fun c hc =>
    _root_.GlobalTheory.KapLat.ExModel.exists_isModel E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) (u₁, u₂) hsep hF c.rep.1 c.rep.2 hc
  let Φ : TwCl (MonoidHom.id (UL n w)) → (B₁.prod B₂).Cl := fun c =>
    if h : ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧ IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 then
      Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ else Quot.mk _ ⟨1, by simp⟩
  have hrep : ∀ c ∈ S', IsModel w e (B₁.prod B₂) (u₁, u₂) (GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c)) c.rep.1 := by
    intro c hc
    have h := hex c hc
    have hΦ : Φ c = Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ := dif_pos h
    have hq := Quot.eqvGen_exact ((Quot.out_eq (Φ c)).trans hΦ)
    obtain ⟨v, hv⟩ := hcl.symm (hcl.eqvGen_iff.1 hq)
    have hr : GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c) = h.choose * ((v : (B₁.prod B₂).A) * (B₁.prod B₂).σ (v : (B₁.prod B₂).A)) := by
      unfold GlobalTheory.UnitLemma.InvAlg.Cl.rep
      rw [hv]
      simp
    rw [hr]
    exact model_mul_norm E w K e (B₁.prod B₂) _ _ n _ h.choose_spec.2.2 v
  let G : (B₁.prod B₂).Cl → ℂ := fun κ =>
    ((K.eta (B₁.gramDet (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ).1) * (B₁.prod B₂).N κ.rep : ℚ) : ℂ)
  have hterm : ∀ c ∈ S', kapSign n w Q₁ c.rep.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) c.rep
      (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = G (Φ c) := by
    intro c hc
    have hm := hrep c hc
    have h7 := _root_.GlobalTheory.KapOrb.twOrb_congruence_eq_N E w hw K e hBr k t ht htk n (Q₁ * Q₂) (B₁.prod B₂) _ _ hsep hF hg.symm c.rep.1 c.rep.2 hm
    simp only [Subtype.coe_eta] at h7
    rw [_root_.GlobalTheory.KapLat.kapSign_eq_eta_gramDet E w hw K e hBr n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ _ _ hm, h7]
    simp [G]
  have hinj : Set.InjOn Φ S' := by
    intro c₁ hc₁ c₂ hc₂ h12
    have m₁ := hrep c₁ hc₁
    have m₂ := hrep c₂ hc₂
    rw [h12] at m₁
    obtain ⟨y, hy, hyc⟩ := _root_.GlobalTheory.KapLat.models_conj E w hw K e (B₁.prod B₂) _ _ n _ _ m₁ m₂
    rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
    exact Quot.sound ⟨⟨y, hy⟩, Subtype.ext (by simpa [TwCl.rep] using hyc)⟩
  have hsupp : Function.support G ⊆ Φ '' S' := by
    intro κ hκ
    have hN : (B₁.prod B₂).N κ.rep ≠ 0 := by
      intro h0; apply hκ; simp [G, h0]
    have hfix : (B₁.prod B₂).σ (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) = GlobalTheory.UnitLemma.InvAlg.Cl.rep κ := (Quot.out κ).2
    have hunit : IsUnit (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) := (Quot.out κ).1.isUnit
    obtain ⟨γ, hγ, hmγ⟩ := _root_.GlobalTheory.KapLat.exists_model_of_N_ne_zero E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) _ _ hF hdeg hfix hunit hN
    have hcp : γ.val.charpoly = Q₁ * Q₂ := _root_.GlobalTheory.KapLat.charpoly_of_model E w K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ γ hmon hF hmγ
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ ⟨γ, hγ⟩
    obtain ⟨g, hg'⟩ := hconj.symm
      (hconj.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq c)))
    have hcrep : c.rep.1 = g.1⁻¹ * γ * g.1 := by
      have := congrArg Subtype.val hg'
      simpa [TwCl.rep] using this
    have hc : c ∈ S' := by
      show c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcrep, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hcp]
    refine ⟨c, hc, ?_⟩
    have m := hrep c hc
    rw [hcrep] at m
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.KapLat.model_conj_norm E w hw K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ _ hsep hF γ g.1 g.2 hmγ m
    exact (Quot.out_eq (Φ c)).symm.trans ((Quot.sound (hcl.symm ⟨v, hv⟩)).trans (Quot.out_eq κ))
  calc _ = ∑ᶠ c, S'.indicator (fun c => G (Φ c)) c := finsum_congr fun c => by
          by_cases hc : c ∈ S'
          · rw [Set.indicator_of_mem hc, ← hterm c hc]
            exact if_pos hc
          · rw [Set.indicator_of_notMem hc]
            exact if_neg hc
    _ = ∑ᶠ c ∈ S', G (Φ c) := (finsum_mem_def _ _).symm
    _ = ∑ᶠ κ ∈ Φ '' S', G κ := (finsum_mem_image hinj).symm
    _ = ∑ᶠ κ, G κ := by
      exact (finsum_mem_inter_support_eq G (Φ '' S') Set.univ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])).trans
        (finsum_mem_univ G)

theorem kapOrb_congruence_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he1 he2 he3 he4 k t ht htk n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
    hadj₁ hae₁ hfr₁ hu₁ hadj₂ hae₂ hfr₂ hu₂
  exact kapOrb_eq_kapSum_of_fits hw ⟨he1, he2, he3, he4⟩ ht htk hsep (hm₁.mul hm₂)
    (by rw [hm₁.natDegree_mul hm₂, hd₁, hd₂, hab]) ⟨hadj₁, hae₁, hfr₁, hu₁⟩ ⟨hadj₂, hae₂, hfr₂, hu₂⟩ (Prod.ext rfl rfl)

end GlobalTheory.KapLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_eq_self_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B)
    (hle : B ≤ A) {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

end Abstract

variable {nS nT : ℕ}

theorem fin_smul_mtF_sub_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ J) : pairA F 0 1 • (mtF σ J g - 1) = 0 := by
  have h : (mtF σ J g).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  apply GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF
  ext i j
  rw [Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.zero_apply, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPartF F E) (finPartF F E).map_zero (finPartF F E).map_one]
  rfl

theorem fin_smul_XFF (x : XFF F E nS nT) : pairA F 0 1 • (x : WOF F E nS nT) = x := by
  have h1 : pairA F 1 0 • (x : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF x.fin
  have h2 : pairA F 0 1 = 1 - pairA F 1 0 := Prod.ext (by show (0 : Ainf F) = 1 - 1; rw [sub_self])
    (by show (1 : Af F) = 1 - 0; rw [sub_zero])
  rw [h2, sub_smul, one_smul, h1, sub_zero]

theorem rhoFF_real {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [coe_rhoFF]
  have hL : mtF σ JT h * (x : WOF F E nS nT) = x := by
    have : (mtF σ JT h - 1) * (x : WOF F E nS nT) = 0 := by
      rw [← fin_smul_XFF x, Matrix.mul_smul, ← Matrix.smul_mul, fin_smul_mtF_sub_one hh, Matrix.zero_mul]
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hR : (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x := by
    have : (x : WOF F E nS nT) * (mtF σ JS g⁻¹ - 1) = 0 := by
      rw [← fin_smul_XFF x, Matrix.smul_mul, ← Matrix.mul_smul,
        fin_smul_mtF_sub_one (Subgroup.inv_mem _ hg), Matrix.mul_zero]
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  show mtF σ JT h * (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x
  rw [hL, hR]

theorem IsLatRepF.real_triv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have key : Om (g, h) = LinearMap.id := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have hfix : Om (g, h) e = e := by
      rw [hR.vac _ e he]
      exact normOp_eq_self_of_le H lam (hR.sd' _)
        (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he
    rw [hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]
  rw [key, LinearMap.id_apply]

end GlobalTheory.FinLatF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_part_left : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  first | exact @GlobalTheory.DoublingEv.PartLTame.isTame_partL | exact GlobalTheory.DoublingEv.PartLTame.isTame_partL | (intros; apply GlobalTheory.DoublingEv.PartLTame.isTame_partL <;> assumption)
end

