module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrStmt
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ChiFinM (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)

def SelfDualP (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllBrTenLe
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

def BlockFockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ) (c : ι → ℝ),
    (∀ τ, ∀ f ∈ V τ, (Formalism.REAL.fockF (F τ f) (F τ f)).re ≤ c τ ^ 2 * (Formalism.REAL.fockF f f).re) →
    ∀ P ∈ Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f},
      (Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P)).re ≤
        (∏ τ, c τ ^ 2) * (Formalism.REAL.fockF P P).re

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def eX {k : ℕ} (l : DomWeight k) : ℝ := (Formalism.REAL.fockF (extremal ℂ k l) (extremal ℂ k l)).re

theorem eX_pos {k : ℕ} (l : DomWeight k) : 0 < eX l := by
  have h := (Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.L2.Ker.lm_extremal_ne (K := ℂ) l)).1
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.ofReal_re] at h
  exact h

theorem normFock_re {k : ℕ} (l : DomWeight k) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    (normFock l f f).re = (Formalism.REAL.fockF f f).re / eX l := by
  unfold normFock eX
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.div_ofReal_re, Complex.ofReal_re]

def cF (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.fm u).beOn τ * Real.sqrt (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ))

theorem cF_sq (τ : D.what₂.Tau) :
    cF D u τ ^ 2 = (D.fm u).beOn τ ^ 2 * (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ)) := by
  unfold cF
  rw [mul_pow, Real.sq_sqrt (div_nonneg (eX_pos _).le (eX_pos _).le)]

theorem factor_le (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hf : f ∈ delSq ℂ _ ((D.fm u).lam D.R.m τ)) :
    (Formalism.REAL.fockF (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
      (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤ cF D u τ ^ 2 * (Formalism.REAL.fockF f f).re := by
  have hI := interlaceTr D u (sg_interlace Tf.valP) τ
  have hI' := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI
  have hf' : f ∈ nablaSq ℂ _ (lamTr D u τ) := by
    rw [Formalism.L2.Col.nablaSq_eq_delSq]; unfold lamTr; rw [delSq_wSh]; exact hf
  have h := Formalism.L2.Ker.nm_le _ _ _ hI' hS f hf'
  have hb : (D.fm u).beOn τ ^ 2 = ((Formalism.L2.Col.Br.cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 *
      Formalism.L2.Col.Br.kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
    rw [beOn_closedS Tf hB τ]
    unfold Formalism.L2.Ker.beOnVal
    rw [mul_pow, sq_abs, Real.sq_sqrt (Formalism.L2.Ker.nm_kapR_pos _ _ _ hI' hS).le]
  have eS : eX (sgTr D u τ) = eX ((D.fm u).sg τ) := by unfold eX sgTr; rw [extremal_wSh]
  have eL : eX (lamTr D u τ) = eX ((D.fm u).lam D.R.m τ) := by unfold eX lamTr; rw [extremal_wSh]
  rw [normFock_re, normFock_re, eS, eL, ← hb] at h
  have hs := eX_pos ((D.fm u).sg τ)
  have hl := eX_pos ((D.fm u).lam D.R.m τ)
  rw [div_le_iff₀ hs] at h
  rw [cF_sq]
  calc _ ≤ (D.fm u).beOn τ ^ 2 * ((Formalism.REAL.fockF f f).re / eX ((D.fm u).lam D.R.m τ)) * eX ((D.fm u).sg τ) := h
    _ = _ := by field_simp

theorem nfAll_brTen_le (hT : BlockFockBound) (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re := by
  have key := hT D.what₂.Tau (D.R.N D.R.m) (D.R.N D.R.m - 1) (fun τ => delSq ℂ _ ((D.fm u).lam D.R.m τ))
    (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (cF D u)
    (fun τ f hf => factor_le Tf hB τ f hf) P hP
  have eprod : ∀ {k : ℕ} (l : D.what₂.Tau → DomWeight k),
      ∏ τ, Formalism.REAL.fockF (extremal ℂ k (l τ)) (extremal ℂ k (l τ)) = ((∏ τ, eX (l τ) : ℝ) : ℂ) := by
    intro k l
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.nm_fockF_self _
  unfold Formalism.L2.Forms.nfAll
  rw [eprod, eprod, Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hs : 0 < ∏ τ, eX ((D.fm u).sg τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hl : 0 < ∏ τ, eX ((D.fm u).lam D.R.m τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hc : ∏ τ, cF D u τ ^ 2 =
      (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => cF_sq τ
  rw [hc] at key
  rw [div_le_iff₀ hs]
  calc (Formalism.REAL.fockF (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re
      ≤ (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) *
          (Formalism.REAL.fockF P P).re := key
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfFixed
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def StabFix (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0

theorem span_with_orthogonal_vector (Tf : FormsTiedSym D u Ch chOf) :
    ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  intro y
  obtain ⟨x, s, hy⟩ := span_iXc_zc D y
  exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩

theorem ext_of_fix (Tf : FormsTiedSym D u Ch chOf) (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)
    (hΓ : cT (sigD D : D.host.E →+* D.host.E) Γ * gramN D D.R.m le_rfl * Γ = gramN D D.R.m le_rfl)
    (hfix : Γ *ᵥ Tf.til.z0 = Tf.til.z0) :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hC := crdFacts_of Tf
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hγ : ∀ x y, hform σ J (Γ *ᵥ x) (Γ *ᵥ y) = hform σ J x y := fun x y => hform_UJ σ J Γ hΓ x y
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth (span_with_orthogonal_vector Tf)
    (by rw [hzz]; exact hT0) Γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show Γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem ext_unique (Tf : FormsTiedSym D u Ch chOf) {δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E}
    {Γ1 Γ2 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (h1 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ1) (h2 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ2) : Γ1 = Γ2 := by
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have hz : (fun a => (RingHom.id D.host.E) (Tf.til.z0 a)) = Tf.til.z0 := rfl
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  rw [hm] at a1 a2
  rw [hz] at b1 b2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  simp only [Matrix.toLin'_apply]
  obtain ⟨x, s, rfl⟩ := span_with_orthogonal_vector Tf y
  have hx : iXc D x = iXm D *ᵥ x := by simp only [iXm, LinearMap.toMatrix'_mulVec]
  rw [hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, b1, b2, mulVec_mulVec, mulVec_mulVec, a1, a2]


set_option maxHeartbeats 4000000 in
theorem stab_back (Tf : FormsTiedSym D u Ch chOf) (hF : StabFix Tf) (c : (D.fm u).clsP) :
    ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  have key : ∀ s : (D.mem u).C.stab D.R.m ((D.fm u).til c), ∃ (s' : (D.fm u).stabilizer₂ c)
      (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ
        ((Tf.til.ga c).1.1 * (Km.stabI ((D.fm u).til c) s).1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (Tf.clsP.stabI c s').1.1 = δ := by
    intro s
    set γ := Km.stabI ((D.fm u).til c) s with hγ
    have hU : cT (sigD D : D.host.E →+* D.host.E) ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *
        gramN D D.R.m le_rfl * ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) = gramN D D.R.m le_rfl := by
      have h0 := (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).2
      have e : (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 =
          (Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
      have h1 : cT (sigD D : D.host.E →+* D.host.E) (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 *
          gramN D D.R.m le_rfl * (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = gramN D D.R.m le_rfl := h0
      rwa [e] at h1
    obtain ⟨δ, hδE, hδi⟩ := ext_of_fix Tf _ hU (hF c γ ⟨s, rfl⟩)
    have hΓu : IsUnit ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
    have hδu := isUnit_of_extE Tf δ _ hΓu hδE
    set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
    have hΔv : Δ.1 = δ := IsUnit.unit_spec _
    have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
      show cT _ Δ.1 * gramP D * Δ.1 = gramP D
      rw [hΔv]; exact unitary_of_hform _ _ _ hδi
    obtain ⟨s', hs'⟩ := stab_restrict Tf c γ ⟨s, rfl⟩ ⟨Δ, hΔ⟩ (by rw [show (⟨Δ, hΔ⟩ : UJ _ _).1.1 = δ from hΔv]; exact hδE)
    exact ⟨s', δ, hδE, by rw [hs']; exact hΔv⟩
  choose g δf hδE hδv using key
  refine ⟨g, fun s1 s2 h12 => ?_⟩
  have hδ12 : δf s1 = δf s2 := by rw [← hδv s1, ← hδv s2, h12]
  have hΓ := ext_unique Tf (hδE s1) (hδ12 ▸ hδE s2)
  apply Km.stabI_inj ((D.fm u).til c)
  apply Subtype.ext
  apply Units.ext
  have hi : ((Tf.til.ga c)⁻¹).1.1 * (Tf.til.ga c).1.1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have := congrArg (fun M => ((Tf.til.ga c)⁻¹).1.1 * M * (Tf.til.ga c).1.1) hΓ
  simp only [← Matrix.mul_assoc, hi, Matrix.one_mul] at this
  simp only [Matrix.mul_assoc, hi, Matrix.mul_one] at this
  exact this

theorem stabiliser_bijective_of_fixed
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      StabFix Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_injection (fun D u Ch chOf Tf c => stab_back Tf (hF D u Ch chOf Tf) c)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

