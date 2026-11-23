module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def cj {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : Hfin X u) : X.B.I.Gf :=
  (X.xu u)⁻¹ * (s : X.B.I.Gf) * X.xu u

def UniSub : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ) (x y : GL (Fin k) F), Formalism.L2.SG.GGMirabolic.IsUni k x →
    Formalism.L2.SG.GGMirabolic.IsUni k y →
      Formalism.L2.SG.GGMirabolic.IsUni k (x * y) ∧ Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹

def IdxHom : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    levi Y.TR (1 : X.B.I.Gf) = 1 ∧
    (∀ s t : Hfin X u, cj X u s ∈ X.B.I.Kset → cj X u t ∈ X.B.I.Kset →
      levi Y.TR (cj X u (s * t)) = levi Y.TR (cj X u s) * levi Y.TR (cj X u t)) ∧
    ∀ s : Hfin X u, cj X u s ∈ X.B.I.Kset → s ∈ Ku X u Y.hK →
      ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi Y.TR (cj X u s) v)

def IdxSurj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ A : Iof Y.TR, ∃ s : Hfin X u, cj X u s ∈ X.B.I.Kset ∧ levi Y.TR (cj X u s) = A

variable {D : D7} {X : HidaSetting D}

theorem kset_inv {m : X.B.I.Gf} (hm : m ∈ X.B.I.Kset) : m⁻¹ ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm ⊢
  simpa using (Formalism.UG.stabGL X.B.I.Lf).inv_mem hm

theorem cj_inv (u : D.what₂.Word) (s : Hfin X u) : cj X u s⁻¹ = (cj X u s)⁻¹ := by
  simp [cj, mul_assoc]

theorem cj_one (u : D.what₂.Word) : cj X u 1 = 1 := by
  simp [cj]

theorem latS_mul_K {u : D.what₂.Word} (h : X.B.I.Gf) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    latS X u (h * (s : X.B.I.Gf)) = latS X u h := by
  ext y
  simp only [latS, Set.mem_setOf_eq]
  have e : (h * (s : X.B.I.Gf) * X.xu u)⁻¹ = (cj X u s)⁻¹ * (h * X.xu u)⁻¹ := by
    simp only [cj]; group
  have hm := kset_inv hs
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm
  have e2 : X.B.I.fmat ((cj X u s)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat (cj X u s)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  rw [e, e2, ← Matrix.mulVec_mulVec]
  exact (hm _).symm

def Uprod (hU : UniSub) (TR : TypedRed X) : Subgroup (Iof TR) where
  carrier := {x | ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (x v)}
  one_mem' := fun _ => Formalism.L2.SG.GGMirabolic.isUni_one
  mul_mem' := fun {a b} ha hb v => (hU _ _ _ _ (ha v) (hb v)).1
  inv_mem' := fun {a} ha v => (hU _ _ _ _ (ha v) (ha v)).2

theorem card_Uprod (hU : UniSub) (TR : TypedRed X) :
    Nat.card (Uprod hU TR) = ∏ v, Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k := by
  have e : ↥(Uprod hU TR) ≃ ∀ v, {x : GL (Fin D.R.k) (TR.Fq v) // Formalism.L2.SG.GGMirabolic.IsUni D.R.k x} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  rfl

theorem card_Iof (TR : TypedRed X) :
    Nat.card (Iof TR) = ∏ v, Fintype.card (GL (Fin D.R.k) (TR.Fq v)) := by
  rw [Nat.card_pi]
  simp [Nat.card_eq_fintype_card]

theorem gamma_one_eq_card (hU : UniSub) (TR : TypedRed X) :
    Gam1 TR = (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) := by
  have hU0 : ∀ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) ≠ 0 := by
    intro v
    have : Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k ≠ 0 := by
      unfold Formalism.L2.SG.GGMirabolic.cardU
      exact Nat.card_ne_zero.mpr ⟨⟨⟨1, Formalism.L2.SG.GGMirabolic.isUni_one⟩⟩, inferInstance⟩
    exact_mod_cast this
  have h1 : ∀ v, Formalism.L2.SG.GGMirabolic.gam (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) =
      (((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) : ℝ) : ℂ) := by
    intro v
    have hp : Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) = 1 := by
      rw [Formalism.L2.SG.GGMirabolic.psiNat, if_pos Formalism.L2.SG.GGMirabolic.isUni_one, Formalism.L2.SG.GGMirabolic.psiU]
      convert AddChar.map_zero_eq_one (TR.psi0 v)
      unfold Formalism.L2.SG.GGMirabolic.superdiag
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with hj
      · show (1 : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
        exact Matrix.one_apply_ne (fun hij => by subst hij; omega)
      · rfl
    rw [Formalism.L2.SG.GGMirabolic.gam]
    simp only [mul_one, mul_inv_cancel, hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    rw [div_eq_inv_mul]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Uprod hU TR)
  rw [card_Iof, card_Uprod] at hq
  have hq' : (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) =
      (∏ v, (Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ)) /
        ∏ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) := by
    rw [eq_div_iff (Finset.prod_ne_zero_iff.mpr fun v _ => hU0 v)]
    exact_mod_cast hq.symm
  rw [hq', ← Finset.prod_div_distrib]
  simp only [Formalism.L2.SG.TermOp.Gam1, Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, h1]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem indexGe_of (hU : UniSub) (hH : IdxHom) (hS : IdxSurj) : IndexGe := by
  intro D X Y u hT Λ hΛ
  classical
  have hlat0 : latS X u (((Y.cs u).h ((Y.cs u).base Λ) : Hfin X u) : X.B.I.Gf) = (Λ : Set (VS D).V) := by
    rw [← lamOf_eq_latS (Y.cs u) ((Y.cs u).base Λ), (Y.cs u).base_lam Λ hΛ]
  have hKmul : ∀ m m' : X.B.I.Gf, m ∈ X.B.I.Kset → m' ∈ X.B.I.Kset → m * m' ∈ X.B.I.Kset := by
    intro m m' hm hm'
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm hm' ⊢
    simpa using (Formalism.UG.stabGL X.B.I.Lf).mul_mem hm hm'
  have cj_mul : ∀ a b : Hfin X u, cj X u (a * b) = cj X u a * cj X u b := by
    intro a b
    simp only [cj, Subgroup.coe_mul]
    group
  obtain ⟨hl1, hlmul, hluni⟩ := hH D X Y u hT
  choose s hsK hsA using hS D X Y u hT
  let e : Fin (Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR)) ≃ (Iof Y.TR ⧸ Uprod hU Y.TR) :=
    (Finite.equivFin _).symm
  refine ⟨Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR),
    fun i => (Y.cs u).h ((Y.cs u).base Λ) * s (Quotient.out (e i)), ?_, ?_, ?_⟩
  · exact le_of_eq (gamma_one_eq_card hU Y.TR)
  · intro i
    rw [Subgroup.coe_mul, latS_mul_K _ _ (hsK _), hlat0]
  · intro i j hij
    have hAi := hsA (Quotient.out (e i))
    have hAj := hsA (Quotient.out (e j))
    have hKa := hsK (Quotient.out (e i))
    have hKb := hsK (Quotient.out (e j))
    set a := s (Quotient.out (e i)) with ha
    set b := s (Quotient.out (e j)) with hb
    have hab : a⁻¹ * b ∈ Ku X u Y.hK := by
      have : ((Y.cs u).h ((Y.cs u).base Λ) * a)⁻¹ * ((Y.cs u).h ((Y.cs u).base Λ) * b) = a⁻¹ * b := by
        group
      rwa [this] at hij
    have hKai : cj X u a⁻¹ ∈ X.B.I.Kset := by
      rw [cj_inv]
      exact kset_inv hKa
    have hKab : cj X u (a⁻¹ * b) ∈ X.B.I.Kset := by
      rw [cj_mul]
      exact hKmul _ _ hKai hKb
    have hinv : levi Y.TR (cj X u a⁻¹) = (levi Y.TR (cj X u a))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hlmul _ _ hKai hKa, inv_mul_cancel, cj_one, hl1]
    have hmem : (Quotient.out (e i))⁻¹ * Quotient.out (e j) ∈ Uprod hU Y.TR := by
      have h2 := hluni _ hKab hab
      rw [hlmul _ _ hKai hKb, hinv, hAi, hAj] at h2
      exact h2
    apply e.injective
    rw [← QuotientGroup.out_eq' (e i), ← QuotientGroup.out_eq' (e j)]
    exact QuotientGroup.eq.mpr hmem

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section LeviHom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem leviM_mul_inv {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : leviM TR x v * leviM TR x⁻¹ v = 1 := by
  rw [← leviM_mul_par TR hx.1 hx.2, mul_inv_cancel, leviM_one]

theorem isUnit_det_leviM {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : IsUnit (leviM TR x v).det :=
  isUnit_iff_exists_inv.2 ⟨(leviM TR x⁻¹ v).det, by rw [← Matrix.det_mul, leviM_mul_inv TR hx, Matrix.det_one]⟩

theorem levi_coe {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = leviM TR x v := by
  unfold levi
  rw [dite_eq_left (isUnit_det_leviM TR hx v)]
  rfl

theorem levi_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : levi TR (x * y) = levi TR x * levi TR y := by
  funext v
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, levi_coe TR (good_mul X hx hy), levi_coe TR hx, levi_coe TR hy,
    leviM_mul_par TR hx.1 hy.1]

theorem levi_one : levi TR (1 : X.B.I.Gf) = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR (good_one X), leviM_one]
  rfl

end LeviHom

section FixAux

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fmat_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem fixes_mul {x y : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) (hy : X.B.I.fmat y *ᵥ v = v) :
    X.B.I.fmat (x * y) *ᵥ v = v := by
  rw [fmat_mul, ← Matrix.mulVec_mulVec, hy, hx]

theorem fixes_inv {x : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) : X.B.I.fmat x⁻¹ *ᵥ v = v := by
  calc X.B.I.fmat x⁻¹ *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ v) := by rw [hx]
    _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]

theorem mem_mL_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (m : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I m) :
    X.B.I.fmat x *ᵥ y ∈ mL X.B.I m := by
  unfold mL at *
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨X.B.I.fmat x *ᵥ w, ?_, ?_⟩
    · exact (hx w).1 hw
    · rw [Matrix.mulVec_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ c ha

theorem congG_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) {δ : VA X.B.I} (hδ : InAt X.B.I X.B.g X.B.g δ) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat x *ᵥ δ - δ) := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  refine ⟨c, hc, ?_⟩
  rw [smul_sub, ← Matrix.mulVec_smul]
  exact Submodule.sub_mem _ (mem_mL_of_Kset X hx _ hcδ) hcδ

end FixAux

section ColGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_hA_mL {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I d w) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (mL_Qs X.B.I X.B.g hw hd)

theorem colStab (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    (∀ a, X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.e0 a - X.e0 a ∈
      mL X.B.I X.B.g) ∧
    X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  set k := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) with hkdef
  obtain ⟨hE0, hF0, hZ0, -, -⟩ := frame_Lf X
  have hk' : k = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by rw [hkdef]; group
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y → X.B.I.fmat k *ᵥ incl X.B.I y = incl X.B.I y := by
    intro y hy hxu
    rw [hk']
    have h1 : X.B.I.fmat (h' : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h'.2 y hy
    have h2 : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := fixes_inv X (h.2 y hy)
    exact fixes_mul X (fixes_inv X hxu) (fixes_mul X h2 (fixes_mul X h1 hxu))
  have hE : ∀ a, X.B.I.fmat k *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) := fun a =>
    hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)) ((X.xu_fix u a).1)
  have hZ : X.B.I.fmat k *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u))) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) := by
    rw [Matrix.mulVec_mulVec, ← fmat_mul]
    have e : k * (X.xu u)⁻¹ = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by rw [hkdef]; group
    rw [e, fmat_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have hy : X.crd (X.zu u) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u := Or.inr rfl
    exact fixes_mul X (fixes_inv X (h.2 _ hy)) (h'.2 _ hy)
  have key : ∀ (w v : VA X.B.I), v ∈ X.B.I.Lf → X.B.I.fmat k *ᵥ w = w → InAt X.B.I X.B.g X.B.g (v - w) →
      X.B.I.fmat k *ᵥ v - v ∈ mL X.B.I X.B.g := by
    intro w v hv hw hvw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hk hv) hv) ?_
    have := congG_of_Kset X hk hvw
    have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - w) - (v - w) := by
      rw [Matrix.mulVec_sub, hw]; abel
    rw [e]; exact this
  refine ⟨fun a => key _ _ (hE0 a) (hE a) (X.basisApprox a).1, key _ _ hZ0 hZ ?_⟩
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  refine ⟨c, hc, ?_⟩
  rw [show X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) =
    -(X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) - X.z0) by abel, smul_neg]
  exact Submodule.neg_mem _ hcm

theorem par_of_stab {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    (he : ∀ a, X.B.I.fmat k *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hie : ∀ a, X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hiz : X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g) : Par X k := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hk, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat k *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k *ᵥ X.e0 a - X.e0 a) by abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (mL_Mo X.B.I (he a))
  · refine mem_Mo_eb X (K_mv X.B.I hk (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a) by abel,
        hA_add_left]
      exact Z_add X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1 (Z_hA_mL X (hie a) (hB j))
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0) by abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (Z_hA_mL X hiz (hB j))
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem colGood (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset)
    (hki : ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    Good X (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by
  have einv : (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) := by group
  have s1 := colStab X u h h' hk
  have s2 := colStab X u h' h hki
  refine ⟨par_of_stab X hk s1.1 (by rw [einv]; exact s2.1) (by rw [einv]; exact s2.2), ?_⟩
  rw [einv]
  have einv2 : (((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) := by group
  exact par_of_stab X hki s2.1 (by rw [einv2]; exact s1.1) (by rw [einv2]; exact s1.2)

end ColGood

end PI.UnitaryDimensionFormula.NormCutK
end
end

