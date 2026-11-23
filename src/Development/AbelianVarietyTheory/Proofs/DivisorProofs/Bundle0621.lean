module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CEval

theorem eq_zero_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Projective O M] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] (y : M)
    (h : ∀ m : ℕ, ∃ z : M, y = ((p : O) ^ m) • z) : y = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  have h0 : s y = 0 := by
    ext i
    refine eq_of_forall_dvd p fun m => ?_
    obtain ⟨z, hz⟩ := h m
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
    exact dvd_mul_right _ _
  have := LinearMap.congr_fun hs y
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at this
  exact this.symm

theorem isHausdorff_of_projective {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  refine ⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩
  have := dvd_of_smodEq p m (hy m)
  rw [sub_zero] at this
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow, map_natCast]

theorem isEval_comp {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (p : ℕ) {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (h : IsEval p x E)
    (g : A →ₐ[R] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A]
    [Algebra R A] (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] {x : σ → A}
    {E : MvPowerSeries σ R →ₐ[R] A} (hE : IsEval p x E) (u : τ → MvPowerSeries σ R)
    (E' : MvPowerSeries τ R →ₐ[R] A) (hu : ∀ j, constantCoeff (u j) = 0)
    (hE' : IsEval p (fun j => E (u j)) E') (f : MvPowerSeries τ R) : E (subst u f) = E' f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
    (fun c => by
      show E (substAlgHom hs (C c)) = E' (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = E' (X j)
      rw [substAlgHom_X, hE'.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hE'.2 f

end GlobalTheory.CEval

namespace GlobalTheory.QLog.Chart

open GlobalTheory.CEval

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ} (c : Chart G d)

omit c in
theorem isHausdorff₂ (G : PDivGroup p O) (n : ℕ) :
    IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
  isHausdorff_of_projective (O := O) p

theorem ev₂_subst_μ (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (subst c.μ s) = Coalgebra.comul (R := O) (c.ev n s) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
  rw [eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n))
    c.isLaw.const ?_ s]
  · rfl
  convert h using 2 with j
  rw [c.comul n j]
  rfl

theorem ev₂_inL (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL s) = c.ev n s ⊗ₜ[O] (1 : G.A n) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O)
    (A := G.A n) (B := G.A n))
  rw [inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i))
    ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  exact ⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩

theorem ev₂_inR (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR s) = (1 : G.A n) ⊗ₜ[O] c.ev n s := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O)
    (A := G.A n) (B := G.A n))
  rw [inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i))
    ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  convert h using 2 with j
  rw [(c.isEval₂ n).1]
  rfl

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem comul_ev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), Coalgebra.comul (R := O) (c.ev n s) = c.ev n s ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] c.ev n s + c.ev₂ n (cob1 c.μ s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n s
  rw [cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]
  abel

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLaw
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMulEndo

variable {R : Type} [CommRing R] {d : ℕ}

theorem hasSubst_elim {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j); exacts [hu j, hv j])

theorem constantCoeff_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim hu hv) (by rintro (j | j); exacts [hu j, hv j]) (hμ i)

theorem subst_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {σ τ : Type}
    {u v : Fin d → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {w : σ → MvPowerSeries τ R} (hw : HasSubst w) :
    (fun i => subst w (op μ u v i)) = op μ (fun i => subst w (u i)) (fun i => subst w (v i)) := by
  funext i
  simp only [op, at2]
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hw]
  congr 1
  funext j
  rcases j with j | j <;> rfl

theorem op_comm {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    op μ b a = op μ a b := by
  funext i
  have hs : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j))) :=
    hasSubst_elim (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  have hab := hasSubst_elim ha hb
  have h := congrArg (subst (Sum.elim a b)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [subst_comp_subst_apply hs hab] at h
  have e : (fun s => subst (Sum.elim a b) (Sum.elim (fun j => (X (Sum.inr j) :
      MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with s | s <;> simp [subst_X hab]
  rw [e] at h
  exact h

theorem op_assoc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) :
    op μ (op μ a b) c = op μ a (op μ b c) := by
  have hW : HasSubst (Sum.elim a (Sum.elim b c)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j | j); exacts [ha j, hb j, hc j])
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
    fun i => subst (Sum.elim a (Sum.elim b c)) (F i)) hμ.assoc
  try simp only at h
  rw [subst_op μ (constantCoeff_op μ hμ.const h1 h2) h3 hW, subst_op μ h1 h2 hW,
    subst_op μ h1 (constantCoeff_op μ hμ.const h2 h3) hW, subst_op μ h2 h3 hW] at h
  simpa [x1, x2, x3, subst_X hW] using h

theorem op_interchange {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c e : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0)
    (he : ∀ i, constantCoeff (e i) = 0) :
    op μ (op μ a b) (op μ c e) = op μ (op μ a c) (op μ b e) := by
  rw [op_assoc hμ ha hb (constantCoeff_op μ hμ.const hc he), ← op_assoc hμ hb hc he,
    op_comm hμ hc hb, op_assoc hμ hc hb he,
    ← op_assoc hμ ha hc (constantCoeff_op μ hμ.const hb he)]

theorem op_zero_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (τ : Type) :
    op μ (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = fun _ => 0 := by
  have hw : HasSubst (fun _ : Fin d => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  have hz : subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (0 : MvPowerSeries (Fin d) R) = 0 := by
    rw [← coe_substAlgHom hw, map_zero]
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d) R =>
    fun i => subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (F i)) hμ.unit
  try simp only at h
  rw [subst_op μ (fun i => constantCoeff_X i) (fun _ => map_zero _) hw] at h
  simpa [subst_X hw, hz] using h

theorem subst_nmul_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) :
    (fun j => subst a (nmul μ 0 j)) = fun _ => 0 := by
  funext j
  show subst a (0 : MvPowerSeries (Fin d) R) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

theorem subst_nmul_succ {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) :
    (fun j => subst a (nmul μ (k + 1) j)) = op μ (fun j => subst a (nmul μ k j)) a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [QLogDefect.nmul_succ, subst_op μ (QLogDefect.constantCoeff_nmul hμ k)
    (fun i => constantCoeff_X i) hs]
  congr 1
  funext i
  exact subst_X hs i

theorem constantCoeff_subst_nmul {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) (j : Fin d) :
    constantCoeff (subst a (nmul μ k j)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (QLogDefect.constantCoeff_nmul hμ k j)

theorem subst_nmul_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (k : ℕ)
    {τ : Type} {a b : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun j => subst (op μ a b) (nmul μ k j)) =
      op μ (fun j => subst a (nmul μ k j)) (fun j => subst b (nmul μ k j)) := by
  have hab := constantCoeff_op μ hμ.const ha hb
  induction k with
  | zero =>
    rw [subst_nmul_zero μ hab, subst_nmul_zero μ ha, subst_nmul_zero μ hb, op_zero_zero hμ]
  | succ k ih =>
    rw [subst_nmul_succ μ hμ.const hab, ih, subst_nmul_succ μ hμ.const ha,
      subst_nmul_succ μ hμ.const hb,
      op_interchange hμ (constantCoeff_subst_nmul μ hμ.const ha k)
        (constantCoeff_subst_nmul μ hμ.const hb k) ha hb]

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  intro R _ d μ hμ k
  refine ⟨QLogDefect.constantCoeff_nmul hμ.const k, fun j => ?_⟩
  have hL : ∀ i, constantCoeff ((fun i => X (Sum.inl i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hR : ∀ i, constantCoeff ((fun i => X (Sum.inr i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hxy : op μ (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inr i)) = μ := by
    funext i
    have e : (Sum.elim (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inr i))) = X := by
      funext s; rcases s with s | s <;> rfl
    show subst _ (μ i) = μ i
    rw [e, subst_self]; rfl
  have h := congrFun (subst_nmul_op hμ k hL hR) j
  rw [hxy] at h
  exact h

end GlobalTheory.NMulEndo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrame
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.NilF

theorem map_inv_transpose_blk {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ)
    (M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) (hM : IsUnit M) (a b : R) (i j : Fin d ⊕ Fin k) :
    f ((M.transpose⁻¹ * blk d k a b) i j) = (((M.map f).transpose)⁻¹ * blk d k (f a) (f b)) i j := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).2
    (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hb : (blk d k a b).map f = blk d k (f a) (f b) := by
    rw [blk, blk, Matrix.diagonal_map (map_zero f)]
    congr 1
    funext l
    rcases l with l | l <;> rfl
  have := congr_fun (congr_fun (Matrix.map_mul (f := f) (L := M.transpose⁻¹)
    (M := blk d k a b)) i) j
  rw [Matrix.map_apply] at this
  rw [this, ← map_inv_of_isUnit f _ hMt, Matrix.transpose_map, hb]

theorem isNil_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hU hV hUV hN
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθτ := theta_tau F hv hε
  have hUV' : U.map F.θ = V.map (WittVector.fontaineTheta O p) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨c, hc⟩ := hUV i j
    rw [Matrix.map_apply, Matrix.map_apply, ← F.θ_a, ← sub_eq_zero, ← map_sub, hc, map_mul, hθτ,
      zero_mul]
  refine isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a _ ?_
  refine isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN
  rw [Matrix.map_apply, F.θ_a, map_inv_transpose_blk F.θ d k U hU, map_inv_transpose_blk _ d k V hV,
    hUV', map_one, map_one, map_natCast, theta_frob_xi hv hε]

end GlobalTheory.WinLift.NilF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
section
noncomputable section

namespace GlobalTheory.ChartCubExt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Exist.CubicalExtension

def ExtendGenAt (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (eA : Sp K ⟶ pullback G.hom (spMap (algebraMap V K))),
      eA ≫ pullback.fst G.hom (spMap (algebraMap V K)) = spMap (algebraMap V K) ≫ eSec G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (pullback.fst G.hom (spMap (algebraMap V K))))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (spMap (algebraMap V K))) →
    ∃ r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (pullback.fst G.hom (spMap (algebraMap V K))) = r

section Group

variable {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]

theorem isPullCubical_of_generic_of_ext (hE : ExtendGenAt T K) {S : Scheme.{0}} {G₀ : Over S} {G : Over (Sp T)}
    {GK : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G] [IsCommMonObj G] [GrpObj GK] [IsCommMonObj GK]
    (hG : IsSemiAbelian G) {L₀ : RigLB G₀} {L : RigLB G} {LK : RigLB GK} (c₀ : CubicalStr G₀ L₀)
    (c : CubicalStr G L) (cK : CubicalStr GK LK) (n : CubeMap G G₀) (m : CubeMap GK G) (m' : CubeMap GK G₀)
    (hp : IsPullback m.F GK.hom G.hom (spMap (algebraMap T K))) (he : m.e = spMap (algebraMap T K))
    (h₁ : m'.F = m.F ≫ n.F) (h₂ : m'.F3 = m.F3 ≫ n.F3) (h₃ : m'.e = m.e ≫ n.e)
    (H' : m.IsPullCubical cK c) (H'' : m'.IsPullCubical cK c₀) : n.IsPullCubical c c₀ := by
  obtain ⟨F, F3, e, he', hp'⟩ := m'
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rw [isPullCubical_iff] at H' H'' ⊢
  obtain ⟨w', g', r', q'⟩ := H'
  obtain ⟨w'', g'', r'', q''⟩ := H''
  have := hG.smooth
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have a₂ : eSec GK ≫ GK.hom = 𝟙 _ := Over.w η[GK]
  obtain ⟨κ, κ', hκ, hκ'⟩ : ∃ (κ : pullback G.hom (spMap (algebraMap T K)) ⟶ GK.left)
      (κ' : GK.left ⟶ pullback G.hom (spMap (algebraMap T K))),
      κ ≫ m.F = pullback.fst G.hom (spMap (algebraMap T K)) ∧ κ' ≫ κ = 𝟙 _ :=
    ⟨hp.isoPullback.inv, hp.isoPullback.hom, hp.isoPullback_inv_fst, hp.isoPullback.hom_inv_id⟩
  have hj : κ' ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.F := by rw [← hκ, ← Category.assoc, hκ', Category.id_comp]
  obtain ⟨r, hr, vr⟩ := exists_quot_of_isos L₀.isLB L.isLB LK.isLB w' w'' g' g'' κ (pullback.fst G.hom (spMap (algebraMap T K))) hκ
  obtain ⟨ρ, hρ, vρ⟩ := exists_quot_of_gens n.e_comm L₀.rig L.rig L₀.rigGen L.rigGen
  have heA : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = spMap (algebraMap T K) ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm, he]
  have heA' : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.e ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm]
  have heκ : (eSec GK ≫ κ') ≫ κ = eSec GK := by rw [Category.assoc, hκ', Category.comp_id]
  obtain ⟨w, hw, hwr⟩ := hE G hG (eSec GK ≫ κ') heA
    ⟨LB.div (L₀.L.pull n.F) L.L, ρ, LB.isLB_div (pull_isLB L₀.isLB _) L.isLB, hρ⟩ r hr (by
      intro J J' _ _ hJ
      obtain rfl : J = J' := funext fun _ => hJ PUnit.unit PUnit.unit heA
      refine unit_ext fun y hy => ?_
      refine (gm_res _ y _ hy _).trans (Eq.trans ?_ (gm_res _ y _ hy _).symm)
      refine (gm_pullGen _ _ _ r _ (𝟙 _) y J hy.1).trans (Eq.trans ?_ (gm_pullGen _ _ _ ρ _ (𝟙 _) y J hy.2).symm)
      obtain ⟨k, hk⟩ := exists_chart LK.isLB (eSec GK y)
      have hm := (mem_qchart (j := (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) (a := (J PUnit.unit).1 PUnit.unit)
        (i := (J PUnit.unit).2)).1 hy.1
      have hm' := hm
      have hm'' := hm
      rw [heA'] at hm'
      rw [Category.assoc, hj] at hm''
      have e₁ := vr _ (eSec GK ≫ κ') y _ _ k hm.1 hm.2 (by
        show ((eSec GK ≫ κ') ≫ κ) y ∈ _
        rw [heκ]; exact hk)
      have e₂ := vρ _ m.e y _ _ hm'.1 hm'.2
      have e₃ := r'' _ (𝟙 _) y (fun _ => (J PUnit.unit).1 PUnit.unit) (fun _ => k) (fun _ => hm''.1) (fun _ => hk)
      have e₄ := r' _ (𝟙 _) y (fun _ => (J PUnit.unit).2) (fun _ => k) (fun _ => hm''.2) (fun _ => hk)
      rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₃ e₄
      rw [heκ] at e₁
      rw [e₃, e₄, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one] at e₂
      rw [Category.id_comp, Category.id_comp]
      refine e₁.trans (e₂.symm.trans ?_)
      rw [he]
      rfl)
  have tri : Tri (L := L₀.L) (L' := L.L) (F := n.F) w w' w'' := by
    intro Y f y a i k ha hi hk
    have p₁ : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) = m.F (f y) := congrArg (fun g => g (f y)) hj
    have p₂ : κ (κ' (f y)) = f y := congrArg (fun g => g (f y)) hκ'
    have ha' : n.F (pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y))) ∈ L₀.L.U a := by rw [p₁]; exact ha
    have hi' : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) ∈ L.L.U i := by rw [p₁]; exact hi
    have e₁ := vr _ (f ≫ κ') y a i k ha' hi' (by
      show κ (κ' (f y)) ∈ _
      rw [p₂]; exact hk)
    have hy : (f ≫ κ') y ∈ qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i := mem_qchart.2 ⟨ha', hi'⟩
    have e₂ : gm (f ≫ κ') y (qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i) (r.s (fun _ => (fun _ => a, i))) =
        gw (L := L₀.L) (L' := L.L) (F := n.F) w ((f ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) y a i := by
      rw [← hwr]
      exact (gm_res _ y _ hy _).trans (gm_pull (f ≫ κ') (pullback.fst G.hom (spMap (algebraMap T K))) y
        ((L₀.L.pull n.F).U (fun _ => a) ⊓ L.L.U i) ⟨mem_pull.2 ha', hi'⟩ _)
    rw [e₂, Category.assoc, Category.assoc, hj, hκ', Category.comp_id] at e₁
    rw [e₁, inv_mul_cancel_right]
  refine ⟨w, (isGen_iff _).1 hw, ?_, ?_⟩
  · refine pmaps_of_tri tri LK.isLB (fun _ => n.e_comm) (fun _ => m.e_comm) r' r'' (𝟙 _) ?_
    rw [Category.id_comp, he]
    exact app_injective_generic (p := 𝟙 _) (q := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  · have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    let P : Over (Sp K) := Over.mk (pullback.snd (G3 G).hom (spMap (algebraMap T K)))
    let x : Fin 3 → (P ⟶ GK) := fun i => Over.homMk
      (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ m.F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 GK := lift (x 0) (lift (x 1) (x 2))
    have hl : l.left ≫ m.F3 = pullback.fst (G3 G).hom (spMap (algebraMap T K)) := hom_ext_triple _ fun i => by
      have : l ≫ x3 GK i = x i := by fin_cases i <;> simp [l, x3]
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, this, hx]
    refine pmaps_of_tri tri LK.isLB (fun I => n.psum_comm I.down) (fun I => m.psum_comm I.down) q' q'' l.left ?_
    rw [hl]
    exact app_injective_generic (IsPullback.of_hasPullback _ _)

end Group

end GlobalTheory.ChartCubExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.Cobd.cobd
  | exact GlobalTheory.EtC.KumPic.Cobd.cobd
  | (intros; apply GlobalTheory.EtC.KumPic.Cobd.cobd <;> assumption)
end

