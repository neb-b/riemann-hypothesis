module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.Twist

theorem halfBlockSum_inv_conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (AE F E), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d v π b hπ g G hG X hdet Y hY
  set B : Matrix (Fin d) (Fin d) (Fv F v) := (b : Matrix (Fin d) (Fin d) (Fv F v)) with hB
  set Bi : Matrix (Fin d) (Fin d) (Fv F v) := ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hBi
  have hBBi : B * Bi = 1 := Units.mul_inv b
  have hBiB : Bi * B = 1 := Units.inv_mul b
  let φ : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).subtype
  have conj : ∀ M : Matrix (Fin d) (Fin d) (Fv F v), B * (Bi * M * B) * Bi = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, Matrix.mul_assoc, hBBi,
      Matrix.mul_one]
  have hGφ : G.map (fun x => (x : Fv F v)) = G.map φ := rfl
  rw [hGφ] at hG
  have h11 : g.toBlocks₁₁.map π = B * G.toBlocks₁₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₁ hG
    rw [Matrix.toBlocks_fromBlocks₁₁] at this
    have e : (G.map φ).toBlocks₁₁ = G.toBlocks₁₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h12 : g.toBlocks₁₂.map π = B * G.toBlocks₁₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₁₂ hG
    rw [Matrix.toBlocks_fromBlocks₁₂] at this
    have e : (G.map φ).toBlocks₁₂ = G.toBlocks₁₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h21 : g.toBlocks₂₁.map π = B * G.toBlocks₂₁.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₁ hG
    rw [Matrix.toBlocks_fromBlocks₂₁] at this
    have e : (G.map φ).toBlocks₂₁ = G.toBlocks₂₁.map φ := rfl
    rw [e] at this; rw [this, conj]
  have h22 : g.toBlocks₂₂.map π = B * G.toBlocks₂₂.map φ * Bi := by
    have := congrArg Matrix.toBlocks₂₂ hG
    rw [Matrix.toBlocks_fromBlocks₂₂] at this
    have e : (G.map φ).toBlocks₂₂ = G.toBlocks₂₂.map φ := rfl
    rw [e] at this; rw [this, conj]
  have hYφ : Y.map π = B * X.map φ * Bi := hY
  set c : Fv F v := π (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) with hc
  have hc2 : (2 : Fv F v) * c = 1 := by
    rw [hc, hπ, ← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  have hsm : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (⅟(2 : AF F) • M).map π = c • M.map π := by
    intro M; ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, Matrix.smul_apply, Matrix.map_apply, hc, smul_eq_mul]
  have aπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M + N).map π = M.map π + N.map π :=
    fun M N => Matrix.map_add π (map_add π) M N
  have sπ : ∀ M N : Matrix (Fin d) (Fin d) (AE F E), (M - N).map π = M.map π - N.map π :=
    fun M N => Matrix.map_sub π (map_sub π) M N
  have aφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M + N).map φ = M.map φ + N.map φ :=
    fun M N => Matrix.map_add φ (map_add φ) M N
  have sφ : ∀ M N : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), (M - N).map φ = M.map φ - N.map φ :=
    fun M N => Matrix.map_sub φ (map_sub φ) M N
  set s := G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ with hs
  set t := G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂ with ht
  set P := s + X * t with hP
  have hSπ : (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂).map π = B * s.map φ * Bi := by
    simp only [aπ, aφ, h11, h12, h21, h22, hs, Matrix.mul_add, Matrix.add_mul]
  have hTπ : (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂).map π = B * t.map φ * Bi := by
    simp only [aπ, sπ, aφ, sφ, h11, h12, h21, h22, ht, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul]
  have hK : (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂) +
      Y * (⅟(2 : AF F) • (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂))).map π
      = c • (B * P.map φ * Bi) := by
    rw [aπ, Matrix.map_mul, hsm, hsm, hSπ, hTπ, hYφ, hP, aφ s (X * t), Matrix.map_mul (f := φ) (M := t) (L := X)]
    rw [Matrix.mul_smul, ← smul_add]
    congr 1
    have : B * X.map φ * Bi * (B * t.map φ * Bi) = B * (X.map φ * t.map φ) * Bi := by
      calc B * X.map φ * Bi * (B * t.map φ * Bi) = B * X.map φ * (Bi * B) * t.map φ * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.add_mul, ← Matrix.mul_add]
  refine ⟨(2 : Fv F v) • (B * (P⁻¹).map φ * Bi), ?_, ?_⟩
  · rw [hK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc2, one_smul]
    have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    calc B * (P⁻¹).map φ * Bi * (B * P.map φ * Bi) = B * ((P⁻¹).map φ * (Bi * B) * P.map φ) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hBiB, Matrix.mul_one, ← Matrix.map_mul, hPinv, Matrix.map_one _ (map_zero φ) (map_one φ),
            Matrix.mul_one, hBBi]
  · intro i j
    have : Bi * ((2 : Fv F v) • (B * (P⁻¹).map φ * Bi)) * B = (2 : Fv F v) • (P⁻¹).map φ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc Bi * (B * (P⁻¹).map φ * Bi) * B = (Bi * B) * (P⁻¹).map φ * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [this, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have e : (2 : Fv F v) * φ (P⁻¹ i j) = φ (2 * P⁻¹ i j) := by rw [map_mul, map_ofNat]
    rw [e]
    exact (2 * P⁻¹ i j).2

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

noncomputable section

namespace GlobalTheory.Asc

variable {D : D7}

theorem symplOH_swap {S T : HSp D} (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  have h := symplOH_self (S := S) (T := T) (x + y)
  rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_self, symplOH_self] at h
  linear_combination h

theorem symplO_swap {S T : HSp D} (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap]; ring

theorem psi_symplO_swap (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x y : WO S T) :
    ψ (symplO S T y x) = 1 ↔ ψ (symplO S T x y) = 1 := by
  rw [symplO_swap, AddChar.map_neg_eq_inv, inv_eq_one]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a b : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T a (heisO ψ S T b f) = ψ (symplO S T a b) • heisO ψ S T b (heisO ψ S T a f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm b a, ← AddChar.map_add_eq_mul,
    GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap a b]
  have e : symplOH S T a b + symplOH S T a b + -symplOH S T a b = symplOH S T a b := by ring
  rw [e]

theorem annVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)),
    (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧
    (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧
    ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ →
      thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  intro D ψ hψ S T Γ
  refine ⟨fun f hf w hw => ?_, fun w hΓ hw => ?_, fun v f f₀ hf hf₀ w hw => ?_⟩
  · refine ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf.1 w, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · show heisO ψ S T (2 • u) (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.1 u hu, (psi_symplO_swap ψ _ _).2 (hw.1 u hu), one_smul]
    · show heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.2 e he u hu hh, (psi_symplO_swap ψ _ _).2 (hw.2 e he u hu hh), one_smul]
  · have key : ∀ u ∈ Γ, symplO S T w u = 0 := fun u hu => by
      rw [GlobalTheory.ThetaSquare.symplO_eq, (symplOH_fin_real (hΓ u hu) hw).2, add_zero]
    refine ⟨fun u hu => ?_, fun e _ u hu _ => by rw [key u hu, AddChar.map_zero_eq_one]⟩
    rw [key _ (Γ.nsmul_mem hu 2), AddChar.map_zero_eq_one]
  · obtain ⟨hμ, h𝓕, -⟩ := v.covol
    have hex : ∃ u, heisO ψ S T u f = f ∧ heisO ψ S T u f₀ = f₀ ∧ ψ (symplO S T w u) ≠ 1 := by
      by_contra hno
      push_neg at hno
      exact hw ⟨fun u hu => hno _ (hf.2.1 u hu) (hf₀.2.1 u hu),
        fun e he u hu hh => hno _ (hf.2.2 e he u hu hh) (hf₀.2.2 e he u hu hh)⟩
    obtain ⟨u, hu, hu₀, hc⟩ := hex
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀.1 w
    have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf.1 hg u
    rw [hu, heisO_comm, hu₀] at e1
    have e2 : GlobalTheory.Ker.ipO v.μ v.𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
        starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) := by
      unfold GlobalTheory.Ker.ipO
      rw [← integral_const_mul]
      congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    have hc' : starRingEnd ℂ (ψ (symplO S T u w)) ≠ 1 := by
      intro h
      apply hc
      have h2 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h2
      exact (psi_symplO_swap ψ _ _).1 h2
    rw [e2] at e1
    show GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0
    have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc')

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatPairInt

variable {D : D7}

theorem cA_tmul (p : AF D.host.F) (t : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] t) = p ⊗ₜ[D.host.F] (star t) :=
  rfl

theorem intAt_zero (P : GlobalTheory.FinPl.Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem pair_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) rfl

theorem term_eq (p q : AF D.host.F) (a g b : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] a) * incA D g * (q ⊗ₜ[D.host.F] b) = (p * q) ⊗ₜ[D.host.F] (star a * g * b) := by
  rw [cA_tmul]
  change (p ⊗ₜ[D.host.F] star a) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * (q ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pairing_mem (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : IsSelfDualC S L) (P : GlobalTheory.FinPl.Pl D → Prop)
    (z w : Fin S.rank → AE D) (hz : z ∈ latV S L P) (hw : w ∈ latV S L P) :
    (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩ := hw
      rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have e : (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [term_eq, pair_mul, one_mul, one_mul]
      show (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) ∈ intAt D P
      rw [e]
      refine ⟨GlobalTheory.FinPlLoc.pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [GlobalTheory.FinPlLoc.finPart_pair]
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, b, rfl⟩
      rw [map_mul]; exact mul_mem (hβi v) (hαi v)
    | zero =>
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact intAt_zero P
    | add w₁ w₂ _ _ h₁ h₂ =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact intAt_add h₁ h₂
    | neg w _ h =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
      exact intAt_neg h
  | zero =>
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact intAt_zero P
  | add z₁ z₂ _ _ h₁ h₂ =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact intAt_add h₁ h₂
  | neg z _ h =>
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    exact intAt_neg h

theorem pairing_mem_at : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) :=
  fun _ S L hL v z w hz hw => pairing_mem S L hL (· = v) z w hz hw

end GlobalTheory.LatPairInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdjLatO

variable {D : D7}

theorem incA_mul_tmul' (g e : D.host.E) (x : AF D.host.F) :
    incA D g * (x ⊗ₜ[D.host.F] e) = x ⊗ₜ[D.host.F] (g * e) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA' (g e : D.host.E) (x : AF D.host.F) :
    (x ⊗ₜ[D.host.F] e) * incA D g = x ⊗ₜ[D.host.F] (e * g) := by
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

def tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun e => x ⊗ₜ[D.host.F] e

theorem rat_mul_tensM (x : AF D.host.F) {l m n : ℕ} (G : Matrix (Fin l) (Fin m) D.host.E)
    (M : Matrix (Fin m) (Fin n) D.host.E) : rat G ⬝ tensM x M = tensM x (G * M) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, incA_mul_tmul', TensorProduct.tmul_sum]

theorem tensM_mul_rat (x : AF D.host.F) {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
    (G : Matrix (Fin m) (Fin n) D.host.E) : tensM x M ⬝ rat G = tensM x (M * G) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, tmul_mul_incA', TensorProduct.tmul_sum]

theorem adj_tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    adj (tensM x M) = tensM x Mᴴ := by
  ext i j; rfl

theorem xi0_inv_smul_starAdj (S T : HSp D) (x : WO S T) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x = giA S ⬝ (adj x ⬝ gA T) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, smul_smul, ← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul]

def genT (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u : Fin n → D.host.E) :
    Matrix (Fin n) (Fin T.rank) (AE D) :=
  Matrix.of fun p q => x ⊗ₜ[D.host.F] (u p * ∑ i, star (t i) * T.gram i q)

theorem genT_add (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u v : Fin n → D.host.E) :
    genT T x t (u + v) = genT T x t u + genT T x t v := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem genT_zero (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) :
    genT T x t (0 : Fin n → D.host.E) = 0 := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.zero_apply, zero_mul, TensorProduct.tmul_zero, Matrix.zero_apply]

theorem starAdj_gen (S T : HSp D) (x : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T
        (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      genT T x t (star a • s) := by
  have e : (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      tensM x ((Matrix.of fun i k => a * t i * star (s k)) * S.gram) := by
    ext i j
    simp only [tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  rw [xi0_inv_smul_starAdj, e, adj_tensM, Matrix.conjTranspose_mul, gram_conjTranspose, gA, tensM_mul_rat, giA,
    rat_mul_tensM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S), Matrix.one_mul]
  ext p q
  simp only [tensM, genT, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', star_star]
  ring

theorem genT_mem_of_mem_span (S T : HSp D) (LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (t : Fin T.rank → D.host.E) (ht : t ∈ LT) (u : Fin S.rank → D.host.E)
    (hu : u ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) :
    genT T (pairA D.host.F 0 α) t u ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  suffices h : ∀ c : 𝓞 D.host.E, genT T (pairA D.host.F 0 α) t (c • u) ∈ latO T S (LT : Set _) (LS' : Set _) P by
    simpa using h 1
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', ha', s', hs', rfl⟩ := hy
    intro c
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a', ha', t, ht, c • s', LS'.smul_mem c hs', ?_⟩
    ext p q
    simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  | zero => intro c; rw [smul_zero, genT_zero]; exact zero_mem _
  | add y z _ _ hy hz => intro c; rw [smul_add, genT_add]; exact add_mem (hy c) (hz c)
  | smul r y _ hy => intro c; rw [smul_smul]; exact hy (c * r)

theorem incA_inv_xi0_smul_starAdj_mem_latO : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  intro D S T LS LS' LT P hA x hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    rw [starAdj_gen]
    exact genT_mem_of_mem_span S T LS' LT P α hα hP t ht _ (hA a ha s hs)
  | zero =>
    rw [xi0_inv_smul_starAdj, adj_zero, Matrix.zero_mul, Matrix.mul_zero]; exact zero_mem _
  | add y z _ _ hy hz =>
    rw [xi0_inv_smul_starAdj] at hy hz ⊢
    rw [adj_add, Matrix.add_mul, Matrix.mul_add]; exact add_mem hy hz
  | neg y _ hy =>
    rw [xi0_inv_smul_starAdj] at hy ⊢
    rw [adj_neg, Matrix.neg_mul, Matrix.mul_neg]; exact neg_mem hy

end GlobalTheory.AdjLatO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianThetaLevelGroupStabilizesSelfDualLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevKFrame

theorem levK_frame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C Lv ΛT hsd hAA βT hfr Pg hPg hJ k κ hk
  obtain ⟨-, hmov, κ', hκ', hc⟩ := hk
  have hmovT := _root_.GlobalTheory.LevMoveAA.isMov_of_isAA D C.X.Λ ΛT (fmt T k) hAA hmov
  have hSt := _root_.GlobalTheory.LevMov.finE_mem_St_of_isMov D T ΛT βT hfr k hmovT
  refine ⟨hSt, fun PP hPP => ?_⟩
  obtain ⟨PP', hPP', hcj⟩ := _root_.GlobalTheory.ConjPlace.exists_conj_place D PP
  have hI : ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ PP'.asIdeal := by
    rw [hPP']; exact hJ κ κ.2 κ' hκ' PP hPP
  have h1 := _root_.GlobalTheory.LevCong.cong_of_frame D C.X.Λ Lv.β Lv.𝔪 PP'.asIdeal Lv.β_mem Lv.β_span (hPP' ▸ hPg PP hPP) (fmt T k) κ' hI hmov hc
  have h2 := _root_.GlobalTheory.LevExt.mulVec_sub_mem_hatV D C.X.Λ (PP'.asIdeal • C.X.Λ) (fmt T k) h1
  obtain ⟨b, hb, h3⟩ := _root_.GlobalTheory.LevkLoc.congr_of_isAA D C.X.Λ ΛT PP'.asIdeal PP'.isPrime hAA (fmt T k) h2
  have h4 := GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence D T ΛT βT hfr k hSt PP' b hb h3
  exact _root_.GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj D T ΛT hsd βT hfr k hSt PP PP' hcj h4

end GlobalTheory.LevKFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPlaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_weilData_twistCharacter_trivial_splitPlaces : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e W g → c g = 1 := by
  first | exact @GlobalTheory.HalfAverage.charTwist_eq_one_at_split | exact GlobalTheory.HalfAverage.charTwist_eq_one_at_split | (intros; apply GlobalTheory.HalfAverage.charTwist_eq_one_at_split <;> assumption)
end

