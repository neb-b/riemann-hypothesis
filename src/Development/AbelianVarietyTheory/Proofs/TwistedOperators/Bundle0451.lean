module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

noncomputable section

namespace GlobalTheory.FockRealNeg

theorem gramAt_negSp {D : D7} (S : HSp D) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.ChiGrid.negSp S) τ = -gramAt D S τ := by
  unfold gramAt
  rw [GlobalTheory.ChiGrid.negSp_gram, Matrix.map_neg _ (map_neg _)]

theorem isCartanInv_neg_one {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G 1) :
    IsCartanInv (-G) (-1) := by
  obtain ⟨-, -, h3⟩ := h
  refine ⟨by simp, by simp, ?_⟩
  simpa using h3

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

end GlobalTheory.FockRealNeg

namespace GlobalTheory.FockRealNeg

theorem om_pureTensorO_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  have hS1 : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have hT1 : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  have hSn : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.ChiGrid.negSp S) τ) (-1) := fun τ => by
    rw [gramAt_negSp]; exact isCartanInv_neg_one (hS1 τ)
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (GlobalTheory.ChiGrid.negSp S) (fun τ => hdet (hSn τ)) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT1 τ)) h hh
  have c1 : ∀ τ, (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ *
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) =
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ :=
    fun τ => by simp
  have c2 : ∀ τ, (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ * compAt θ τ (Formalism.L2.Theta.mt T h) =
      compAt θ τ (Formalism.L2.Theta.mt T h) * (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ :=
    fun τ => by simp
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hom.std (GlobalTheory.ChiGrid.negSp S) T θ hθ χS χT om η hη hom
    (fun _ => -1) (fun _ => 1) hSn hT1 g hg h hh c1 c2 x y hx hy f hf hv
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have b2 : ∀ τ, BT τ * (BT τ)⁻¹ = 1 := fun τ => by
    have hB : BT τ * ((BT τ)ᴴ * gramAt D T τ) = 1 := mul_eq_one_comm.1 (hBT τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hneg := _root_.GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hom.std hθ BS
    (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ) BT
    (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) f hf P
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (GlobalTheory.ChiGrid.negSp S) T χS χT om hom hθ (fun _ => -1) (fun _ => -1) BS
      (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ))
      (fun _ => 1) (fun _ => 1) BT (fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ)) g h c1 c2
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b2, Matrix.one_mul]) f hf P).2,
    hvac, GlobalTheory.FockCompactAction.pureTensorO_smul, hneg]
  congr 1
  simp only [detPlus_neg_one_one, Finset.prod_const_one, mul_one]
  have hx' : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ : ℤ) : ℚ) := fun τ => by
    have e : ((-e₂ τ : ℤ) : ℚ) = b τ - (T.rank : ℚ) / 2 := by push_cast; rw [he₂]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (hη.2.2.2 τ) _
  have hy' : ∀ τ, HasInfExp D (χS * (η ^ (GlobalTheory.ChiGrid.negSp S).rank)⁻¹) τ ((e₁ τ : ℤ) : ℚ) := fun τ => by
    rw [he₁]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (ha τ) (hη.2.2.2 τ) _
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ (fun τ => -e₂ τ) hx', hyv _ e₁ hy', ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [_root_.zpow_neg, inv_inv]

end GlobalTheory.FockRealNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrMove

open GlobalTheory.SplitHecke GlobalTheory.AdelicLatMove

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  show _ * (x + y) * _ = _ * x * _ + _ * y * _
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

private lemma isHalf_iff_smul_eq {e : AE D} (u : WO S T) : IsHalf e u ↔ e • u = u := by
  unfold IsHalf
  constructor
  · intro hu
    apply Matrix.ext
    intro i j
    change e * u i j = u i j
    exact hu i j
  · intro hu i j
    have h := congrFun (congrFun hu i) j
    change e * u i j = u i j at h
    exact h

private lemma isHalf_actO_twisted_operators {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [isHalf_iff_smul_eq] at hu ⊢
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]

private lemma actO_inv_actO_twisted_operators (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (u : WO S T) :
    IsHalf e (actO S T g h u) ↔ IsHalf e u := ⟨fun hu => by simpa only [actO_inv_actO_twisted_operators] using isHalf_actO_twisted_operators g⁻¹ h⁻¹ hu, isHalf_actO_twisted_operators g h⟩

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨hsupp, k, hk, hper, hden⟩ := hΨ
  refine ⟨fun t ht => (isHalf_actO_iff g h t).1 (hsupp _ ht), k, hk, ?_, fun t ht => ?_⟩
  · intro u hu hue t
    show Ψ (actO S T g h (t + k • u)) = Ψ (actO S T g h t)
    rw [actO_add, actO_nsmul]
    exact hper _ ((hΛ u).1 hu) ((isHalf_actO_iff g h u).2 hue) _
  · rw [hΛ, actO_nsmul]
    exact hden _ ht

theorem halfInd_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) : halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have hc : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
    rw [← hΛ t, isHalf_actO_iff]
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos (hc.2 ht), if_pos ht]
  · rw [if_neg (fun h' => ht (hc.1 h')), if_neg ht]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  unfold heisO
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_move {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) f₀ = c • f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀
      (c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) := by
  obtain ⟨htr, hmod, hvac⟩ := hTm
  have hSB : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf a Λ fun t => Φ (actO S T g h t) := fun Φ hΦ => isSBHalf_comp hΛ hΦ
  have hback : ∀ w : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa only [inv_inv] using actO_inv_actO g⁻¹ h⁻¹ w
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · have hx' : IsHalf a (actO S T g⁻¹ h⁻¹ x) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hx)
    have e1 : Tm (fun s => Φ (actO S T g h s + x)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ x) (Tm fun s => Φ (actO S T g h s)) := by
      have := htr _ (hSB Φ hΦ) _ hx'
      simpa only [actO_add, hback] using this
    show c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s + x))) =
      heisO ψ S T x (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e1, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have hy' : IsHalf (cA D a) (actO S T g⁻¹ h⁻¹ y) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hy)
    have e2 : Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ y) (Tm fun s => Φ (actO S T g h s)) := by
      rw [← hmod _ (hSB Φ hΦ) _ hy']
      congr 1
      funext s
      rw [← symplO_actO S T g h s (actO S T g⁻¹ h⁻¹ y), hback]
    show c⁻¹ • om (g, h) (Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s))) =
      heisO ψ S T y (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e2, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have e3 : (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s)) = (1 : ℂ) • halfInd a Λ := by
      funext s
      simp only [Pi.smul_apply, halfInd_comp hΛ]
    show c⁻¹ • om (g, h) (Tm (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s))) = f₀
    rw [e3, hvac, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem smul_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT a ha ha0 g h hΛ f₀ Φ f c d hf₀ hth hc h0 hΦ
  obtain ⟨⟨Tm, hTm⟩, huniq⟩ := hth
  have hfT : f = Tm Φ := huniq Tm hTm
  have hthT := fun Ψ hΨ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hS hT a ha ha0 f₀ hf₀ Tm hTm Ψ hΨ
  have hf' := huniq _ (isPlaceModel_move hW hΛ hTm hthT hc h0)
  have hcomp : (fun x => Φ (actO S T g h x)) = d • Φ := by
    funext x
    simp only [hΦ, Pi.smul_apply, smul_eq_mul]
  have key : f = c⁻¹ • (d • om (g, h) f) := by
    refine hf'.trans ?_
    show c⁻¹ • om (g, h) (Tm (fun x => Φ (actO S T g h x))) = c⁻¹ • (d • om (g, h) f)
    rw [hcomp, map_smul, map_smul, ← hfT]
  calc d • om (g, h) f = c • (c⁻¹ • (d • om (g, h) f)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • f := by rw [← key]

end GlobalTheory.SchrMove

end
end

