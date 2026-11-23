module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.PsiStep

section Red
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem q_mem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne_zero : ((qOf P : ℕ) : E) ≠ 0 := by
  have h : qOf P ≠ 0 := by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  exact_mod_cast h

theorem intAt_q : IntAt P (qOf P : E) := by
  have := IntAt.coe P ((qOf P : ℕ) : 𝓞 E)
  rwa [map_natCast] at this

theorem reduction_natCast_eq_zero : redP P (qOf P : E) = 0 := by
  have := reduction_coe P ((qOf P : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (q_mem P)

theorem pow_red (k : ℕ) : IntAt P ((qOf P : E) ^ (k + 1)) ∧ redP P ((qOf P : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_q P, reduction_natCast_eq_zero P⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_q P), by rw [reduction_mul ih.1 (intAt_q P), ih.2, zero_mul]⟩

theorem reduction_one' : redP P (1 : E) = 1 := by
  have := reduction_coe P 1
  rwa [map_one, map_one] at this

theorem valuation_one₂ : LocE.vP P (qOf P) (1 : E) = 0 := by
  have hq0 := q_ne_zero P
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (qOf P : E) ^ z)) :=
    ⟨0, by rw [zpow_zero, div_one, reduction_one']; exact isUnit_one⟩
  have hspec : IsUnit (redP P ((1 : E) / (qOf P : E) ^ LocE.vP P (qOf P) (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P (qOf P) (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (qOf P : E) ^ (k' + 1))
    · have e : (qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1)) = 1 := by field_simp
      have h0 : redP P ((qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1))) = 0 := by
        rw [reduction_mul (pow_red P k').1 hI', (pow_red P k').2, zero_mul]
      rw [e, reduction_one'] at h0
      exact one_ne_zero h0
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, one_mul, (pow_red P k').2] at hspec
    exact not_isUnit_zero hspec

theorem locChar_one_ne {K : Type} [Field K] (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) :
    LocE.locChar (qOf P) cq χ (1 : E) ≠ 0 := by
  unfold LocE.locChar
  rw [valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [reduction_one']; exact isUnit_one)]
  exact Units.ne_zero _

end Red

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Mat
variable {E : Type} [Field E]

theorem joinCol_apply {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (v : Fin (n' + c') → E) (i : Fin n) :
    joinCol (c' := c') (c := c) x₀ y' v (Fin.castAdd c i) =
      x₀ (fun l => v (Fin.castAdd c' l)) i + atNL E (n' + c') n' v * y' i := by
  simp [joinCol, Loc.inX, LinearMap.funLeft]
  rfl

end Mat

theorem om_one_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (Φ : Matrix b a k → ℂ) :
    om μ 1 1 Φ = Φ := by
  funext x
  simp [om, nabs]

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

theorem withCol_toLoc {E k : Type} [Field E] [NumberField E] [StarRing E]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
    {A B : Type} {n' n c' c : ℕ} (e : A ≃ Fin n) (e' : B ≃ Fin n') (hc' : c' = 0 + 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) :
    withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι ((e.sumCongr (finCongr hc.symm)).trans finSumFinEquiv) ((e'.sumCongr (finCongr hc'.symm)).trans finSumFinEquiv)
        (joinCol (c' := c') (c := c) x₀ y') := by
  subst hc' hc
  ext (r | r) (j | j)
  · simp only [withCol, fromBlocks_apply₁₁, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.castAdd (0 + 1) (e' j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = Pi.single (e' j) 1 := by
      funext l
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.castAdd (0 + 1) (e' j)) 1) = 0 := by
      have hj := (e' j).isLt
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
      rw [if_neg (by omega)]
    rw [h1, h2, zero_mul, add_zero]
  · simp only [withCol, fromBlocks_apply₁₂, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = 0 := by
      funext l
      have hl := l.isLt
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
      rw [if_neg (by omega)]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) 1) = 1 := by
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_natAdd]
      rw [if_pos (by omega)]
    rw [h1, map_zero, Pi.zero_apply, h2, one_mul]
    rw [zero_add (y' (e r))]
    rfl
  · exact r.elim0
  · exact r.elim0

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Main
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem omPhi_one_one (i : ℕ) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P 1 1 x = PhiAt Ch mu cst.sharp i P.1 x := by
  have hm : muAt Ch sel mu cst i P 1 ≠ 0 := by
    unfold muAt
    exact locChar_one_ne _ _ _
  unfold omPhi Loc.om
  rw [map_one, map_one, Units.val_one, valuation_one₂]
  rw [mul_inv_cancel₀ hm]
  simp only [neg_zero, zero_mul, zpow_zero, one_mul]
  rfl

end Main

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge


open PsiStep in
theorem psiAgree_of_atType : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν _ hA e' e he' he
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  have hrS : R.rS = S.ρ := by
    have := S.odd
    unfold Ranks.rS; rw [hA.steps]; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; rw [hA.steps]; omega
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hPhi := _root_.GlobalTheory.SymBridge.PhiAgreeProof.phiAgree X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hA.tie
    R.t s 0 rfl (R.N s) (cOf R s) (R.N (s + 1)) (cOf R (s + 1)) rfl rfl hc1 hc0 E' E₁ hE' hE₁
  refine ⟨1, one_ne_zero, fun x₀ y' => ?_⟩
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') := by
    exact withCol_toLoc ι e e' hc1 hc0 x₀ y'
  rw [one_mul, Chain.Psi, om_one_one, hmat, hPhi, PsiAt, omPhi_one_one]
  unfold PhiAt
  rw [if_pos hA.mem, if_pos hA.sharp, hrS, hr]

end GlobalTheory.SymBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralPositionOneEqFiniteSum
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.UnfoldSumBd
open GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.UnfoldSum

theorem val_inv_pow_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1)
    {N A : ℕ} (h : N ≤ A) :
    valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
  have e : (((ϖ ^ N)⁻¹ : kˣ) : k) = (ϖ : k) ^ (A - N) * (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rw [show A = (A - N) + N from (Nat.sub_add_cancel h).symm, pow_add]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [e, map_mul, map_pow]
  exact mul_le_of_le_one_left zero_le' (pow_le_one' hv.le _)

theorem val_pow_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (hv : valuation k (ϖ : k) < 1)
    {N B : ℕ} (h : N ≤ B) : valuation k ((ϖ : k) ^ B) ≤ valuation k ((ϖ : k) ^ N) := by
  rw [show B = N + (B - N) by omega, pow_add, map_mul]
  exact mul_le_of_le_one_right zero_le' (by rw [map_pow]; exact pow_le_one' hv.le _)

theorem sumAgreeBd : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (ψ : AddChar k Circle) (ν : Measure k)
    (psi : E → K) (N : ℕ),
    GlobalTheory.SymBridge.IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → HasConductor ψ 1 → IsUnitVol ν →
    (∀ a, IntAt P ((q : E) ^ N * a) → (ψ (ι a) : ℂ) = σ₀ (psi a)) →
    ∀ (U' U : Type) [Fintype U'] [DecidableEq U'] [Fintype U] [DecidableEq U] (c n' c' n c₂ A B : ℕ),
      1 ≤ c → c' = c + 1 → c₂ = c → N ≤ A → N ≤ B →
    ∀ (d' : U' ≃ Fin n') (d : U ≃ Fin n) (e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : U ⊕ Fin c ≃ Fin (n + c₂)),
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d' a).val) n') e' →
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d a).val) n) e →
    ∀ (Φ : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k → ℂ) (ΦE : Loc.SF E K (n' + c') (n + c₂)) (C : ℂ),
      (∀ x, Φ (GlobalTheory.SymBridge.toLoc ι e e' x) = C * σ₀ (ΦE x)) →
      (∀ x, Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k)) →
      (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ N)) → Φ (x + y) = Φ x) →
      ∀ x₀, opE ψ ν 1 Φ (GlobalTheory.SymBridge.toLoc ι d d' x₀) =
        C * σ₀ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c₂) psi (LocE.valsQ E q A B) (((q : K) ^ B)⁻¹) ΦE x₀) := by
  intro E K k _ _ _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ ν psi N hC hU hψ hν hpsi U' U _ _ _ _ c n' c' n c₂ A B hc hc' hc₂ hA hB
    d' d e' e hoe' hoe Φ ΦE C hΦ hsupp hper x₀
  subst c' c₂
  classical
  have hq : ι (q : E) = (ϖ : k) := hC.unif.symm
  obtain ⟨-, -, -, -, -, -, hres, hrep⟩ := GlobalTheory.SymBridge.ComplRes.residues E k P q ι ϖ hC hU
  have hv : valuation k (ϖ : k) < 1 := (hU ϖ).2 le_rfl
  have hψ1 : ∀ b : k, valuation k b ≤ 1 → ψ b = 1 := fun b hb =>
    (hψ 1).2 le_rfl b (by simpa using hb)
  have hA0 : ((ϖ : k) ^ A) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hinv : (((ϖ ^ A)⁻¹ : kˣ) : k) = ((ϖ : k) ^ A)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hιv : ∀ i : ℕ, ι ((i : E) / (q : E) ^ A) = (i : k) * ((ϖ : k) ^ A)⁻¹ := fun i => by
    rw [map_div₀, map_pow, map_natCast, hq, div_eq_mul_inv]
  set T : Finset k := (LocE.valsQ E q A B).image ι with hTdef
  have hmemT : ∀ t, t ∈ T ↔ ∃ i : ℕ, i < q ^ (A + B) ∧ (i : k) * ((ϖ : k) ^ A)⁻¹ = t := fun t => by
    simp only [hTdef, LocE.valsQ, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (hιv i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hιv i⟩
  have hnat : ∀ i : ℕ, valuation k (i : k) ≤ 1 := fun i => by
    rw [← Valuation.mem_integer_iff]; exact natCast_mem _ i
  have hT1 : ∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := (hmemT t).1 ht
    rw [hinv, map_mul]
    exact mul_le_of_le_one_left zero_le' (hnat i)
  have hT2 : ∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) →
      ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro x hx
    have hz : x * (ϖ : k) ^ A ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k x * valuation k ((ϖ : k) ^ A)
          ≤ valuation k (((ϖ : k) ^ A)⁻¹) * valuation k ((ϖ : k) ^ A) := by
            rw [← hinv]; gcongr
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hA0, map_one]
    obtain ⟨i, ⟨hi, hzi⟩, huniq⟩ := hrep (A + B) _ hz
    have key : ∀ j : ℕ, valuation k (x - (j : k) * ((ϖ : k) ^ A)⁻¹) ≤ valuation k ((ϖ : k) ^ B) ↔
        valuation k (x * (ϖ : k) ^ A - (j : k)) ≤ valuation k ((ϖ : k) ^ (A + B)) := fun j => by
      have e1 : x * (ϖ : k) ^ A - (j : k) = (x - (j : k) * ((ϖ : k) ^ A)⁻¹) * (ϖ : k) ^ A := by
        field_simp
      rw [e1, pow_add, mul_comm ((ϖ : k) ^ A) ((ϖ : k) ^ B), map_mul, map_mul (valuation k) ((ϖ : k) ^ B)]
      have : valuation k ((ϖ : k) ^ A) ≠ 0 := by simpa using hA0
      exact (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 this)).symm
    refine ⟨(i : k) * ((ϖ : k) ^ A)⁻¹, ⟨(hmemT _).2 ⟨i, hi, rfl⟩, (key i).2 hzi⟩, ?_⟩
    rintro t ⟨ht, htx⟩
    obtain ⟨j, hj, rfl⟩ := (hmemT t).1 ht
    rw [huniq j ⟨hj, (key j).1 htx⟩]
  set X₀ := toLoc ι d d' x₀ with hX₀
  let F : ({rs : (U ⊕ Fin c) × (U' ⊕ Fin (c + 1)) // Free 1 rs} → k) → ℂ :=
    fun u => Φ (affPt 1 X₀ u) * (ψ (-ch (affPt 1 X₀ u)) : ℂ)
  have hF1 : ∀ u, F u ≠ 0 → ∀ i, valuation k (u i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) := by
    intro u hu i
    have h1 : Φ (affPt 1 X₀ u) ≠ 0 := left_ne_zero_of_mul hu
    have := hsupp _ h1 i.1.1 i.1.2
    rw [affPt_free] at this
    exact this.trans (val_inv_pow_le ϖ hv hA)
  have hF2 : ∀ u y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (u + y) = F u := by
    intro u y hy
    simp only [F, affPt_add, ch_add]
    have hy' : ∀ r s, valuation k (freeMat y r s) ≤ valuation k ((ϖ : k) ^ N) := by
      intro r s
      simp only [freeMat, Matrix.of_apply]
      split_ifs with h
      · exact (hy _).trans (val_pow_le ϖ hv hB)
      · rw [map_zero]; exact zero_le'
    rw [hper _ _ hy']
    congr 1
    rw [neg_add, AddChar.map_add_eq_mul, hψ1 (-ch (freeMat y)) (by rw [Valuation.map_neg]; exact ch_freeMat_int ϖ hv y hy), mul_one]
  have key := GlobalTheory.PeriodicIntegral.integral_eq_sum k ν hν ϖ hU A B T hT1 hT2 _ F hF1 hF2
  have hL : opE ψ ν 1 Φ X₀ = ∫ u, F u ∂(Measure.pi fun _ => ν) := rfl
  rw [hL, key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Loc.E1, map_mul, map_pow, map_inv₀, map_natCast, map_sum, hres]
  rw [Fintype.card_congr (freeEquiv hc hoe hoe'), mul_left_comm C]
  congr 1
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij (fun t rs => ι (t (freeEquiv hc hoe hoe' rs))) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Fintype.mem_piFinset] at ht ⊢
    exact fun rs => Finset.mem_image_of_mem ι (ht _)
  · intro a _ b _ hab
    funext p
    have := congrFun hab ((freeEquiv hc hoe hoe').symm p)
    simp only [Equiv.apply_symm_apply] at this
    exact ι.injective this
  · intro u hu
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hu
    choose g hg1 hg2 using fun a => Finset.mem_image.1 (hu a)
    refine ⟨fun p => g ((freeEquiv hc hoe hoe').symm p), ?_, funext fun rs => ?_⟩
    · rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact fun p => hg1 _
    · simp only [Equiv.symm_apply_apply, hg2]
  · intro t _
    simp only [F]
    rw [affPt_eq ι hc hoe hoe' x₀ t, hΦ, ch_eq ι hoe hoe']
    set X := Loc.xx1 x₀ t
    rw [← mul_assoc]
    by_cases h0 : C * σ₀ (ΦE X) = 0
    · rw [h0, zero_mul, zero_mul]
    congr 1
    have hnz : Φ (toLoc ι e e' X) ≠ 0 := by rw [hΦ]; exact h0
    have hI := hsupp _ hnz
    have hint : ι ((q : E) ^ N * Loc.chArg X) ∈ 𝒪[k] := by
      rw [map_mul, map_pow, hq, ← ch_eq ι hoe hoe', ch, Finset.mul_sum]
      refine sum_mem fun i _ => ?_
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ : k) ^ N) * valuation k (toLoc ι e e' X (Sum.inr i) (Sum.inr i.succ))
          ≤ valuation k ((ϖ : k) ^ N) * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by gcongr; exact hI _ _
        _ = 1 := by
          rw [← map_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
            mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), map_one]
    have hIA : IntAt P ((q : E) ^ N * -Loc.chArg X) :=
      (hC.int _).1 (by rw [mul_neg, map_neg]; exact neg_mem hint)
    have h2 := hpsi _ hIA
    rw [← h2, map_neg]
end GlobalTheory.UnfoldSumBd
end
end

