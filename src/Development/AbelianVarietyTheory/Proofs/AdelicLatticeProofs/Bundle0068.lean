module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorL_intertwine {ι X : Type} (p : (X → ℂ) → Prop) (p0 : p 0) (padd : ∀ a b, p a → p b → p (a + b))
    (psmul : ∀ (c : ℂ) a, p a → p (c • a)) (A A' : ι → (X → ℂ) → (X → ℂ)) (Φ : Module.End ℂ (X → ℂ))
    (hA : ∀ i f, p f → p (A i f) ∧ Φ (A i f) = A' i (Φ f)) (f : X → ℂ) (hf : p f) (P : MvPolynomial ι ℂ) :
    p (pureTensorL A f P) ∧ Φ (pureTensorL A f P) = pureTensorL A' (Φ f) P := by
  have hl : ∀ l : List ι, p (l.foldr (fun i g => A i g) f) ∧
      Φ (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A' i g) (Φ f) := by
    intro l
    induction l with
    | nil => exact ⟨hf, rfl⟩
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih.2]
      exact hA i _ ih.1
  have hm : ∀ (B : ι → (X → ℂ) → (X → ℂ)) (g : X → ℂ) (k : ι →₀ ℕ) (c : ℂ),
      pureTensorL B g (MvPolynomial.monomial k c) = c • opPow B k g := by
    intro B g k c
    have e : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
  induction P using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [hm, hm, map_smul]
    exact ⟨psmul c _ (hl _).1, congrArg (c • ·) (hl _).2⟩
  | add P Q hP hQ =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hP.2, hQ.2]
    exact ⟨padd _ _ hP.1 hQ.1, rfl⟩

theorem cplxO_move {m n : ℕ} {sS sS' G G' : Matrix (Fin n) (Fin n) ℂ} {sT sT' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (hS : sS' * G = G * sS) (hT : sT' * H = H * sT) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS' sT' (H * z * G') = H * cplxO sS sT z * G' := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have e : G' * sS' = sS * G' := by
    calc G' * sS' = G' * (sS' * G) * G' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]
      _ = sS * G' := by rw [hS, ← Matrix.mul_assoc, hG', Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc sT' * (H * z * G') * sS' = (sT' * H) * z * (G' * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, e]; simp only [Matrix.mul_assoc]

theorem unitMap_move {m n : ℕ} {B G G' : Matrix (Fin n) (Fin n) ℂ} {B' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (i : Fin m) (j : Fin n) : unitMap (G * B) (H * B') i j = H * unitMap B B' i j * G' := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hG]
  simp only [Matrix.mul_assoc]

theorem om_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' BS BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' BT BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ τ, BS' τ = compAt θ τ (mt S g) * BS τ) → (∀ τ, BT' τ = compAt θ τ (mt T h) * BT τ) → ∀ f, IsThetaFunO ψ S T f → ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧ om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS' sT' BS' BT' (om (g, h) f) P := by
  intro D ψ θ S T χS χT om hom hθ sS sS' BS BS' sT sT' BT BT' g h h1 h2 h3 h4 f hf P
  refine pureTensorL_intertwine (IsThetaFunO ψ S T) theta_zero (fun _ _ => theta_add) (fun c _ => theta_smul c) _ _
    (om (g, h)) (fun k f hf => ?_) f hf P
  obtain ⟨τ, i, j⟩ := k
  have hG := compAt_mt_mul_inv (θ := θ) τ g
  refine ⟨theta_smul _ (theta_sub (theta_dRho hθ hom.std τ _ hf) (theta_smul _ (theta_dRho hθ hom.std τ _ hf))), ?_⟩
  simp only [aPlusAll, aPlus, crea]
  rw [map_smul, map_sub, map_smul, om_dRho hom hθ g h τ _ hf, om_dRho hom hθ g h τ _ hf, h3, h4, unitMap_move hG,
    cplxO_move hG (h1 τ) (h2 τ)]

end GlobalTheory.OrientedHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalPointsFinitePartSelfDualLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.RatSelfDual

variable {D : D7}

def symplB (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => symplO S T x y) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 x))
    (fun x x' => AddMonoidHom.ext fun y => (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 x x' y)

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T x (N • y) = symplO S T (N • x) y := by
  have h1 : symplO S T x (N • y) = N • symplO S T x y := (symplB S T x).map_nsmul N y
  have h2 : symplO S T (N • x) y = N • symplO S T x y := ((symplB S T).flip y).map_nsmul N x
  rw [h1, h2]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]

theorem psi_real {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    ψ (symplO S T x y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  rw [symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]
  congr 1
  ring

theorem psi_fin_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, ha⟩ := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y
  have h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1 := by rw [ha]; exact hψ.1.2.2.1 a
  have hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have e1 := psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)
  have e2 := psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)
  rw [hσ.pi_iota, piW_ratW hθ] at e1
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at e2
  have d1 : symplO S T (ratW T S x) (ratW T S y) =
      symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)
  have d2 : symplO S T (finRat S T x) (ratW T S y) =
      symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm] at h1
  exact h1

theorem psi_fin_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) = 1 ↔ ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  have h := psi_fin_mul hψ S T x y
  constructor
  · intro h1
    rw [h1, one_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [hn]; push_cast; ring
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
      rw [hk, Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; ring⟩
    rwa [h2, mul_one] at h

theorem eq_zero_of_parts {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {z : WO S T}
    (hf : z.map (finPart D) = 0) (hi : z.map (infPart D) = 0) : z = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_
  have : infPart D (z i j) = 0 := congrFun (congrFun hi i) j
  rw [this, RingHom.map_zero]

theorem exists_div {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ γ : WO S T, γ.map (infPart D) = 0 ∧ N • γ = u := by
  refine ⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩
  · funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0
    rw [RingHom.map_mul, this, mul_zero]
  · funext i j
    show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j
    have h1 : (N : AE D) = incA D (N : D.host.E) := (map_natCast (incA D) N).symm
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]

theorem finRat_mem_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  intro D S T ψ Λ hψ hinf hdual happ hden x
  constructor
  · intro hx y hy
    exact (psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)
  · intro h
    refine (hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_
    obtain ⟨θ, hθ⟩ := hψ.2.1
    obtain ⟨N, hN, hNx⟩ := hden x
    obtain ⟨γ, hγ, hNγ⟩ := exists_div (hinf u' hu') hN
    obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
    have hz0 : γ - finRat S T y₀ - u = 0 := by
      refine eq_zero_of_parts hθ ?_ ?_
      · funext i j
        have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
        have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
        show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub] at e0 ⊢
        rw [e1, e0]
      · funext i j
        have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
        have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
        have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
        show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]
    have hγe : γ = finRat S T y₀ + u := by
      rw [sub_sub] at hz0
      exact sub_eq_zero.1 hz0
    have hu'e : u' = finRat S T (N • y₀) + N • u := by
      rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]
    have hmem : finRat S T (N • y₀) ∈ Λ := by
      have : finRat S T (N • y₀) = u' - N • u := (sub_eq_of_eq_add hu'e).symm
      rw [this]
      exact Λ.sub_mem hu' (Λ.nsmul_mem hu N)
    rw [hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul,
      symplO_nsmul]
    exact (hdual _ (hinf _ hNx)).1 hNx u hu

end GlobalTheory.RatSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_two_nsmul (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, actO_add]

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO (e : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have e1 : e • x = x := Matrix.ext hx
  have e2 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  exact fun i j => congrFun (congrFun e2 i) j

theorem sqNormIntegralFundamentalDomain_eq_l2Norm_sq (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} (hf : Continuous f) :
    nrm2 μ 𝓕 f = (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ).toReal := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    (hf.norm.pow 2).measurable.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem isVacO_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS LS' : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ u : WO S T, u ∈ (latO S T LS' LT' fun _ => True) ↔ ∃ u₀ ∈ (latO S T LS LT fun _ => True), u = actO S T g h u₀) → ∀ f, IsVacO ψ θ S T sS sT LS LT f → IsVacO ψ θ S T sS' sT' LS' LT' (om (g, h) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sS' sT sT' LS LS' LT LT' g h hS hT hΛ f hf
  obtain ⟨hψ, -, hth, hlat, hfock, hnorm⟩ := hf
  refine ⟨hψ, hθ, hW.om_pres _ _ hth, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← actO_two_nsmul, ← hW.om_heis g h _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := isHalf_actO e g⁻¹ h⁻¹ hh
      rwa [actO_inv_actO] at this
    rw [← hW.om_heis g h _ f hth, hlat.2 e he u₀ hu₀ h0]
  · obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt θ τ (mt T h) * z₀ * compAt θ τ (mt S g⁻¹) := by
      refine ⟨compAt θ τ (mt T h⁻¹) * z * compAt θ τ (mt S g), ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        compAt_mt_mul_inv, Matrix.mul_one]
    have h0 := congrArg (om (g, h)) (hfock τ z₀)
    unfold annih at h0 ⊢
    rw [map_add (f := _), map_smul, map_zero, om_dRho hW hθ g h τ _ hth, om_dRho hW hθ g h τ _ hth] at h0
    rw [cplxO_move θ τ g h (hS τ) (hT τ)]
    exact h0
  · show nrm2 p.1 p.2 (om (g, h) f) = 1
    rw [sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ (hW.om_pres _ _ hth).cont, hW.om_unit p.1 p.2 hp.1 hp.2.1 _ f hth, ← sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hth.cont]
    exact hnorm.2 p hp

end GlobalTheory.WeilVacMove

end
end

