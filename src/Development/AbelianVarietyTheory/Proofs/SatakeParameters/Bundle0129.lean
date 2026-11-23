module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompleteSquareDiagonalNegPowUniformizer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsAtPrimeUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivUnique

section Abstract

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

theorem read_one {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {B B' : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B' *ᵥ z)
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧ B.map φ *ᵥ w = B'.map φ *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨z, hz, e⟩ := h2 _ (h1 (s ∘ w) fun i => hO' _ (hw i))
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc B.map φ *ᵥ w = φ ∘ (B *ᵥ (s ∘ w)) := by rw [mv, ss]
    _ = φ ∘ (ε • (ε • B *ᵥ (s ∘ w))) := by rw [sm, sm]
    _ = φ ∘ (ε • B' *ᵥ z) := by rw [e]
    _ = B'.map φ *ᵥ (φ ∘ z) := by rw [sm, mv]

theorem read_step {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B B' : Matrix (Fin n) (Fin n) R} {u u' : Fin n → R}
    (h4 : ∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ ε • A *ᵥ y = ε • B *ᵥ (fun i => u i * z i))
    (h3 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • A *ᵥ y = ε • B' *ᵥ (fun i => u' i * z i))
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧
      (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w =
        (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have hu : ∀ u z : Fin n → R, φ ∘ (fun i => u i * z i) = Matrix.diagonal (fun i => φ (u i)) *ᵥ (φ ∘ z) :=
    fun u z => funext fun i => by simp [Matrix.mulVec_diagonal]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨y, hy, e⟩ := h4 (s ∘ w) fun i => hO' _ (hw i)
  obtain ⟨z, hz, e'⟩ := h3 y hy
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w
      = φ ∘ (B *ᵥ (fun i => u i * (s ∘ w) i)) := by rw [mv, hu, ss, Matrix.mulVec_mulVec]
    _ = φ ∘ (ε • B *ᵥ (fun i => u i * (s ∘ w) i)) := (sm _).symm
    _ = φ ∘ (ε • B' *ᵥ (fun i => u' i * z i)) := by rw [← e, e']
    _ = (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ (φ ∘ z) := by
      rw [sm, mv, hu, Matrix.mulVec_mulVec]

theorem coset (OK : Subring K) {b b' c c' T T' U : Matrix (Fin n) (Fin n) K}
    (hb : c * b = 1) (hb' : c' * b' = 1) (hT : T' * T = 1)
    (H1 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b *ᵥ y = b' *ᵥ z)
    (H2 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b' *ᵥ y = b *ᵥ z)
    (H3 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b * T) *ᵥ y = (b' * U) *ᵥ z)
    (H4 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b' * U) *ᵥ y = (b * T) *ᵥ z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range,
      k₁.1 * T * k₂.1 = U := by
  obtain ⟨M, hM⟩ := GlobalTheory.PlaceDiv.exists_factor OK b b' H1
  obtain ⟨N, hN⟩ := GlobalTheory.PlaceDiv.exists_factor OK b' b H2
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b * T) (b' * U) H3
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b' * U) (b * T) H4
  have hMN : M.map OK.subtype * N.map OK.subtype = 1 := by
    calc M.map OK.subtype * N.map OK.subtype = c' * b' * (M.map OK.subtype * N.map OK.subtype) := by
          rw [hb', Matrix.one_mul]
      _ = c' * (b' * M.map OK.subtype * N.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = c' * b' := by rw [← hM, ← hN]
      _ = 1 := hb'
  have hl : T' * c * (b * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, hb, Matrix.one_mul, hT]
  have hNM : N₂.map OK.subtype * M₂.map OK.subtype = 1 := by
    calc N₂.map OK.subtype * M₂.map OK.subtype
        = T' * c * (b * T) * (N₂.map OK.subtype * M₂.map OK.subtype) := by rw [hl, Matrix.one_mul]
      _ = T' * c * (b * T * N₂.map OK.subtype * M₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = T' * c * (b * T) := by rw [← hN₂, ← hM₂]
      _ = 1 := hl
  obtain ⟨k₁, hk₁, e₁⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK M N hMN
  obtain ⟨k₂, hk₂, e₂⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK N₂ M₂ hNM
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e₁, e₂]
  calc M.map OK.subtype * T * N₂.map OK.subtype = c' * b' * (M.map OK.subtype * T * N₂.map OK.subtype) := by
        rw [hb', Matrix.one_mul]
    _ = c' * (b' * M.map OK.subtype * T * N₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
    _ = c' * (b' * U) := by rw [← hM, ← hN₂]
    _ = U := by rw [← Matrix.mul_assoc, hb', Matrix.one_mul]

end Abstract


set_option maxHeartbeats 1000000 in
theorem div_unique : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d' := by
  intro D V P e f ϖ d d' g hP h1 h2 hd hd' hD hD'
  have he : e * e = e := by
    rcases id hP with ⟨hs, -⟩ | ⟨rfl, -⟩
    · exact hs.1.1
    · exact ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P _ _ hP).1
  obtain ⟨φ, s, hs, hε, -, hO, hO', hinc⟩ :=
    GlobalTheory.SphLabelOps.exists_component he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP)
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  rw [GlobalTheory.DivDual.divAt_iff] at hD hD'
  obtain ⟨l, B, b1, b2, b3, b4⟩ := hD
  obtain ⟨l', B', b1', b2', b3', b4'⟩ := hD'
  obtain ⟨C, -, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  obtain ⟨C', -, c2'⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B' hee fun y hy => (b2' y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  have hv : Formalism.UG.IsUnifV D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have h0 := Formalism.UG.P.cartan_unif_ne_zero D.host.E P _ hv
  have e1 : ∀ a : List ℤ, (Matrix.diagonal fun i : Fin V.rank =>
      φ (finPart D (incA D ((ϖ : D.host.E) ^ (a.getD i.1 0))))) =
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => a.getD i.1 0 := by
    intro a
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    rw [hinc, map_zpow₀]
  have hinv : (Matrix.diagonal fun i : Fin V.rank => (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) ^ (-(d.getD i.1 0))) *
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) (fun i : Fin V.rank => d.getD i.1 0) = 1 := by
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := coset (Formalism.UG.Ov D.host.E P) (b := B.map φ) (b' := B'.map φ)
    (c := C.map φ) (c' := C'.map φ)
    (T := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d.getD i.1 0)
    (U := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d'.getD i.1 0)
    (mp _ _ c2) (mp _ _ c2') hinv
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1 b2')
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1' b2)
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4 b3')
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4' b3)
  have anti : ∀ a : List ℤ, a.length = V.rank → a.Pairwise (fun a b => b ≤ a) →
      Antitone fun i : Fin V.rank => a.getD i.1 0 := by
    intro a la ha i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have hi : i.1 < a.length := by rw [la]; exact i.2
      have hj : j.1 < a.length := by rw [la]; exact j.2
      simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact List.pairwise_iff_getElem.1 ha _ _ hi hj hlt
  have key := Formalism.UG.Final.CartanUnique D.host.E P V.rank _ (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le hv
    _ _ (anti d l hd) (anti d' l' hd') k₁ hk₁ k₂ hk₂ hk
  refine List.ext_getElem (l.trans l'.symm) fun i hi hi' => ?_
  have := congrFun key ⟨i, by rw [← l]; exact hi⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] using this

end GlobalTheory.DivUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralGramOfPhaseConditions
section
noncomputable section
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Square

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem star_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) :
    (Matrix.transpose (A.map σ)) i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  change Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact h

theorem gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L}
    {n n' : ℕ} {A B : Matrix (Fin n) (Fin n) L} {ψ : AddChar L ℂ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (hAB : A * B = 1) (hAh : ∀ i j, σ (A i j) = A j i)
    (hδ : Valued.v δ = 1 ∧ σ δ = -δ) (hpi : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L)
    (hx : (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1)) :
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * A * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := _root_.GlobalTheory.Hk3.smith_int_approx L ϖ hU.2.2.2.1 n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hA'i : ∀ i j, (Q' * A * Matrix.transpose (Q'.map σ)) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hQ' hA) (star_int hv hQ')
  have hB'i : ∀ i j, (Matrix.transpose (Q.map σ) * B * Q) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int (star_int hv hQ) hB) hQ
  have h1 : Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ) = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hA'B' : (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q) = 1 := by
    calc (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q)
        = Q' * A * (Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ)) * B * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_assoc Q' A B, hAB, Matrix.mul_one, hQ'Q]
  have hAm : A.map σ = Matrix.transpose A := by ext i j; simp [hAh]
  have hQm : (Q'.map σ).map σ = Q' := by ext i j; simp [hσ]
  have hA'h : ∀ i j, σ ((Q' * A * Matrix.transpose (Q'.map σ)) i j) = (Q' * A * Matrix.transpose (Q'.map σ)) j i := by
    have hm : (Q' * A * Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose (Q' * A * Matrix.transpose (Q'.map σ)) := by
      have hQt : (Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose Q' := by ext i j; simp [hσ]
      rw [Matrix.map_mul, Matrix.map_mul, hAm, hQt]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  have hy := _root_.GlobalTheory.phaseCondition_basisChange L σ δ n n' A ψ P Q Q' hσ hv hP hQ' hQQ' x hx
  have hD := _root_.GlobalTheory.Hk3.ShiftPhase.shift L ϖ σ q δ n n' _ ψ hU hq hA'i hδ.1 hδ.2 hpi (P * x * Q) _ hE hy
  rw [sub_sub_cancel] at hD
  obtain ⟨l', hl', hG⟩ := _root_.GlobalTheory.Hk3.SquareDiag.square_diag L ϖ σ q δ n n' _ _ ψ hU hq hA'i hB'i hA'B' hA'h hδ hpi hne a hD
  refine ⟨P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q', ?_, ?_⟩
  · intro i j
    exact mul_int (mul_int hP' (fun i j => add_mem (hE i j) (hl' i j))) hQ' i j
  · have hxe : x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q' := by
      have hx0 : x = P' * (P * x * Q) * Q' := by
        simp only [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        rw [← Matrix.mul_assoc, hP'P, Matrix.one_mul]
      rw [show x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * (P * x * Q) * Q' - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' from by rw [← hx0]]
      have hab : P * x * Q - ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') = (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l' := by abel
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hab]
    rw [hxe]
    have hg : (P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q') * A * Matrix.transpose ((P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q').map σ) =
        P' * (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l').map σ)) * Matrix.transpose (P'.map σ) := by
      simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hg]
    exact mul_int (mul_int hP' hG) (star_int hv hP')

end GlobalTheory.Hk3.HoweDuality.Square

theorem GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q δ n n' JS ψ hU hq hJS hJh hδ hpi hne x hx
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have glint_entry : ∀ {g : GL (Fin n) L}, g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j,
      (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro g hg i j
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
    exact (k.val i j).2
  have hJi : (JS⁻¹ : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := Subgroup.inv_mem _ hJS
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) := by
    ext i j; simp [hJh]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have hJP : (JS : Matrix (Fin n) (Fin n) L) * P = 1 := by rw [hPdef]; exact JS.mul_inv
  have e1 : P.map σ * Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have e2 : (JS : Matrix (Fin n) (Fin n) L) * Matrix.transpose (P.map σ) = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e3 : Matrix.transpose (P.map σ) = P := by
    calc Matrix.transpose (P.map σ) = (P * (JS : Matrix (Fin n) (Fin n) L)) * Matrix.transpose (P.map σ) := by
          rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  have hPh : ∀ i j, σ (P i j) = P j i := by
    intro i j
    have := congrFun (congrFun e3 j) i
    simpa using this
  exact GlobalTheory.Hk3.HoweDuality.Square.gen hU hq (glint_entry hJi) (glint_entry hJS) hPJ hPh hδ hpi hne x hx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem finSigmaFinEquiv_val_eq_range {s : ℕ} (t : Fin s → ℕ) (x : (a : Fin s) × Fin (t a)) :
    ((finSigmaFinEquiv x : Fin (∑ a, t a)) : ℕ) =
      (∑ i ∈ Finset.range x.1, (fun i : ℕ => if h : i < s then t ⟨i, h⟩ else 0) i) + x.2 := by
  rw [finSigmaFinEquiv_apply]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < s := lt_of_lt_of_le i.2 x.1.2.le
  simp only [hi, dif_pos]
  rfl

theorem finSigmaFinEquiv_lt_of_lex_lt {s : ℕ} (t : Fin s → ℕ) (x y : (a : Fin s) × Fin (t a))
    (hxy : toLex x < toLex y) :
    (finSigmaFinEquiv x : Fin (∑ a, t a)) < finSigmaFinEquiv y := by
  rw [Fin.lt_def, finSigmaFinEquiv_val_eq_range, finSigmaFinEquiv_val_eq_range]
  set t' : ℕ → ℕ := fun i => if h : i < s then t ⟨i, h⟩ else 0 with ht'
  rcases Sigma.Lex.lt_def.mp hxy with h | ⟨h, h2⟩
  · have h' : (x.1 : ℕ) < y.1 := h
    have hsub : Finset.range (x.1 + 1) ⊆ Finset.range y.1 :=
      Finset.range_subset_range.mpr h'
    have hle : (Finset.range (x.1 + 1)).sum t' ≤ (Finset.range y.1).sum t' :=
      Finset.sum_le_sum_of_subset hsub
    replace hle := (Finset.sum_range_succ t' x.1).symm.trans_le hle
    have hx : t' x.1 = t x.1 := by simp [ht', x.1.2]
    have h3 : (x.2 : ℕ) < t x.1 := x.2.2
    have h4 : (∑ i ∈ Finset.range x.1, t' i) = (Finset.range x.1).sum t' := rfl
    omega
  · obtain ⟨a, i⟩ := x
    obtain ⟨b, j⟩ := y
    change a = b at h
    subst h
    change i < j at h2
    have : (i : ℕ) < j := h2
    simp only
    omega

theorem finSigmaFinEquiv_symm_strictMono_lex :
    ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) =>
      (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  intro s t c d hcd
  by_contra hn
  rw [not_lt] at hn
  rcases hn.lt_or_eq with h | h
  · have := finSigmaFinEquiv_lt_of_lex_lt t _ _ h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hcd (not_lt.mpr this.le)
  · have h' : finSigmaFinEquiv.symm d = finSigmaFinEquiv.symm c := toLex.injective h
    have := finSigmaFinEquiv.symm.injective h'
    exact absurd hcd (by rw [this]; exact lt_irrefl _)

end GlobalTheory
end

