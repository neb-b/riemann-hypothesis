module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.RealCoordCusp

theorem normSq_det_UJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Complex.normSq (uMat g).det = 1 := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star (uMat g).det * (uMat g).det = 1 := by
    have : (star (uMat g).det * (uMat g).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hJ
  have h3 : ((Complex.normSq (uMat g).det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

variable (I : AutInst)

abbrev Idx : Type := Σ _ : Fin I.n, Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)

def cBasis : Module.Basis (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) ℝ (InfinitePlace I.F → Fin I.n → ℂ) :=
  Pi.basis fun _ => Pi.basis fun _ => Complex.basisOneI

theorem card_eq : Fintype.card (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) = Fintype.card (Idx I) := by
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]
  ring

def rho : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin (Fintype.card (Idx I)) → ℝ) :=
  ((cBasis I).reindex (Fintype.equivFinOfCardEq (card_eq I))).equivFun

theorem rho_isRealCoord : IsRealCoord I (rho I) := by
  intro x y
  simp only [rho, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, dotProduct]
  rw [(Fintype.equivFinOfCardEq (card_eq I)).symm.sum_comp
    (fun s => (cBasis I).repr x s * (cBasis I).repr y s)]
  simp only [cBasis, Fintype.sum_sigma, Pi.basis_repr, Complex.coe_basisOneI_repr, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bQ : Module.Basis (Idx I) ℚ (Fin I.n → I.E) := Pi.basis fun _ => integralBasis I.E

def eB : Fin (Fintype.card (Idx I)) → Fin I.n → I.E := fun k => bQ I ((Fintype.equivFin (Idx I)).symm k)

theorem bQ_apply (p : Idx I) : bQ I p = Pi.single p.1 (integralBasis I.E p.2) := by
  simp [bQ, Pi.basis_apply]

theorem eB_isZBasis : IsZBasis I (eB I) := by
  refine ⟨((bQ I).linearIndependent.comp _ (Fintype.equivFin (Idx I)).symm.injective).restrict_scalars' ℤ, ?_⟩
  intro u
  constructor
  · intro hu
    have hm := Formalism.L2.SG.Pf.Tau.mem_integral_vectors I I.n u (fun k => ⟨⟨u k, hu k⟩, rfl⟩)
    rw [Formalism.L2.SG.Pf.Tau.t8O, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨fun k => c ((Fintype.equivFin (Idx I)).symm k), ?_⟩
    rw [← hc, ← (Fintype.equivFin (Idx I)).symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [eB, bQ_apply]
  · rintro ⟨z, rfl⟩ i
    rw [← mem_integralClosure_iff]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine zsmul_mem ?_ _
    rw [eB, bQ_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mem_integralClosure_iff, integralBasis_apply]
      exact (RingOfIntegers.basis I.E _).isIntegral_coe
    · exact zero_mem _

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bm (y : I.Ginf) : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (uMat (y v)⁻¹)).restrictScalars ℝ).comp (LinearMap.proj v)

theorem vec_eq (y : I.Ginf) (u : Fin I.n → I.E) : GlobalTheory.CuspGeo.vec I y u = bm I y (GlobalTheory.CuspGeo.vec I 1 u) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  simp [GlobalTheory.CuspGeo.vec, bm, h1]

theorem det_bm (y : I.Ginf) : LinearMap.det (bm I y) = 1 := by
  rw [bm, LinearMap.det_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  exact normSq_det_UJ _

theorem gm_eq {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) :
    gm I ρ y e = LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) * gm I ρ 1 e := by
  ext i j
  rw [Matrix.mul_apply]
  change ρ (GlobalTheory.CuspGeo.vec I y (e j)) i = (LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) *ᵥ
    (fun k => ρ (GlobalTheory.CuspGeo.vec I 1 (e j)) k)) i
  rw [LinearMap.toMatrix'_mulVec]
  simp [vec_eq I y]

theorem det_gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : (gm I ρ y e).det = (gm I ρ 1 e).det := by
  rw [gm_eq, Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_conj, det_bm, one_mul]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def qm : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (I.P v)⁻¹).restrictScalars ℝ).comp (LinearMap.proj v)

def sw : (Fin I.n × InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun z := fun v i => z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem qm_injective : Function.Injective (qm I) := by
  intro x y h
  funext v
  have h0 := congrFun h v
  simp only [qm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at h0
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h2 := congrArg (fun w => I.P v *ᵥ w) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

theorem sw_injective : Function.Injective (sw I) := by
  intro x y h
  funext q
  exact congrFun (congrFun h q.2) q.1

theorem vec_one_bQ (p : Idx I) :
    GlobalTheory.CuspGeo.vec I 1 (bQ I p) = qm I (sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p)) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  have h2 : (fun i => I.φ v (bQ I p i)) = sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p) v := by
    funext i
    rw [bQ_apply, Pi.single_apply]
    change _ = Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p (i, v)
    rw [Formalism.L2.SG.Pf.Tau.placeCoordsBasis_apply]
    split_ifs with h
    · subst h; rfl
    · exact map_zero _
  simp only [GlobalTheory.CuspGeo.vec, Pi.one_apply, inv_one, h1, Matrix.one_mulVec]
  rw [h2]
  rfl

theorem det_gm_one_ne : (gm I (rho I) 1 (eB I)).det ≠ 0 := by
  have hli : LinearIndependent ℝ (fun j => (gm I (rho I) 1 (eB I))ᵀ j) := by
    have hf : LinearMap.ker ((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) = ⊥ :=
      LinearMap.ker_eq_bot.2 ((rho I).injective.comp ((qm_injective I).comp (sw_injective I)))
    have h := ((Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n).linearIndependent.map' _ hf).comp _
      (Fintype.equivFin (Idx I)).symm.injective
    have heq : (fun j => (gm I (rho I) 1 (eB I))ᵀ j) =
        ((⇑((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) ∘ ⇑(Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n)) ∘
          ⇑(Fintype.equivFin (Idx I)).symm) := by
      funext j
      funext i
      simp only [Matrix.transpose_apply, gm, Matrix.of_apply, Function.comp_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe]
      rw [eB, vec_one_bQ]
    rw [heq]
    exact h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

end GlobalTheory.RealCoordCusp


open GlobalTheory.RealCoordCusp in
theorem GlobalTheory.CuspGeo.covolume_const : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E)
    (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ),
    0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  intro I
  refine ⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I,
    rho_isRealCoord I, fun y => by rw [det_gm]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropic
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.UG

namespace GlobalTheory.CuspGeo

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hg : cT s g * J * g = J) (x y : Fin n → A) : hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have h1 : ∀ x y : Fin n → A, hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := fun x y => by
    simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Function.comp_apply]
  have h2 : s ∘ (g *ᵥ x) = g.map s *ᵥ (s ∘ x) := funext fun i => RingHom.map_mulVec s g x i
  rw [h1, h1, h2]
  conv_rhs => rw [← hg, ← mulVec_mulVec, ← mulVec_mulVec, cT, mulVec_transpose]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

theorem inUnipRad_conj (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA WA' : Submodule A (Fin I.n → A)) (g gi m : Matrix (Fin I.n) (Fin I.n) A) (hgi : gi * g = 1)
    (hU : ∀ x y, hform s JA (g *ᵥ x) (g *ᵥ y) = hform s JA x y) (h1 : ∀ x ∈ WA, g *ᵥ x ∈ WA')
    (h2 : ∀ y ∈ WA', ∃ x ∈ WA, y = g *ᵥ x) (hm : I.InUnipRad s JA WA' m) :
    I.InUnipRad s JA WA (gi * m * g) := by
  obtain ⟨m1, m2, m3⟩ := hm
  have e : gi * m * g - 1 = gi * (m - 1) * g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgi]
  have e' : ∀ z, (gi * m * g - 1) *ᵥ z = gi *ᵥ ((m - 1) *ᵥ (g *ᵥ z)) := fun z => by
    rw [e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have back : ∀ x, gi *ᵥ (g *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hgi, one_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
  · rw [e', m1 _ (h1 x hx), mulVec_zero]
  · have hy' : g *ᵥ y ∈ {y | ∀ x ∈ WA', hform s JA x y = 0} := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := h2 x' hx'
      rw [hU]; exact hy x hx
    obtain ⟨x, hx, hxe⟩ := h2 _ (m2 _ hy')
    rw [e', hxe, back]; exact hx
  · rw [e', ← hU, mulVec_mulVec _ g gi, mul_eq_one_comm.1 hgi, one_mulVec]
    exact m3 (g *ᵥ y) _ (h1 x hx)

theorem span_map_mulVec {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} (c : Matrix (Fin n) (Fin n) E)
    (W : Submodule E (Fin n → E)) :
    (∀ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)),
      c.map ι *ᵥ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))) ∧
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)),
      ∃ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)), y = c.map ι *ᵥ x := by
  have key : ∀ w : Fin n → E, (c.map ι *ᵥ fun i => ι (w i)) = fun i => ι ((c *ᵥ w) i) := fun w =>
    funext fun i => (RingHom.map_mulVec ι c w i).symm
  constructor
  · intro x hx
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))).comap
          (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, mulVecLin_apply, key]
      exact Submodule.subset_span ⟨c *ᵥ w, ⟨w, hw, rfl⟩, rfl⟩
    exact this hx
  · intro y hy
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _))).map (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨w, hw, rfl⟩, by rw [mulVecLin_apply, key]; rfl⟩
    obtain ⟨x, hx, rfl⟩ := this hy
    exact ⟨x, hx, rfl⟩

theorem naconj : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧
    ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  intro I γ hγ W hW
  obtain ⟨c, hcU, hinf, hfin⟩ := hγ
  have hcU' : cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (c : Matrix (Fin I.n) (Fin I.n) I.E) =
      I.J := hcU
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨W.map (c : Matrix (Fin I.n) (Fin I.n) I.E).mulVecLin, ⟨?_, ?_⟩, fun m hm => ?_⟩
  · intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
    have : (c : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = 0 := by
      rw [← Submodule.mem_bot I.E, ← h]
      exact ⟨w, hw, rfl⟩
    apply hw0
    rw [← one_mulVec w, ← c.inv_mul, ← mulVec_mulVec, this, mulVec_zero]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hform_mulVec_mulVec _ _ _ hcU']
    exact hW.2 x hx y hy
  obtain ⟨hmi, hmf⟩ := hm
  refine ⟨fun v => ?_, ?_⟩
  · have hst : ∀ y : I.E, I.φ v (star y) = star (I.φ v y) := fun y => hcm.2.2.2 (I.φ v) y
    have hPd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have hPP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hPd
    have hPP' : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPd
    have hg : I.P v * uMat (γ.1 v) * (I.P v)⁻¹ = (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) := by
      rw [hinf v, Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP',
        Matrix.one_mul]
    have hu : ∀ a : Formalism.REAL.UJ (I.ε v), uMat a⁻¹ * uMat a = 1 := fun a => by simp [uMat]
    have hmul : ∀ a b : Formalism.REAL.UJ (I.ε v), uMat (a * b) = uMat a * uMat b := fun a b => by simp [uMat]
    have hgi : (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) = 1 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
      rw [← Matrix.mul_assoc (uMat _), hu, Matrix.one_mul, hPP']
    have hconj : I.P v * uMat ((γ⁻¹ * m * γ).1 v) * (I.P v)⁻¹ = (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) *
        (I.P v * uMat (m.1 v) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) := by
      show I.P v * uMat ((γ.1 v)⁻¹ * m.1 v * γ.1 v) * (I.P v)⁻¹ = _
      rw [hmul, hmul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
    have hU : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.J.map (I.φ v) *
        (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      have e : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
          (cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) := by
        ext a b
        simp only [cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
        exact (hst _).symm
      rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hcU']
    obtain ⟨s1, s2⟩ := span_map_mulVec (I.φ v) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ (hmi v)
    · rw [hg]; exact hform_mulVec_mulVec _ _ _ hU
    · rw [hg]; exact s1
    · rw [hg]; exact s2
  · have hfm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by simp [AutInst.fmat]
    have hgi : I.fmat γ.2⁻¹ * I.fmat γ.2 = 1 := by rw [← hfm, inv_mul_cancel]; simp [AutInst.fmat]
    have hconj : I.fmat (γ⁻¹ * m * γ).2 = I.fmat γ.2⁻¹ * I.fmat m.2 * I.fmat γ.2 := by
      show I.fmat (γ.2⁻¹ * m.2 * γ.2) = _
      rw [hfm, hfm]
    have hU : cT (sigR I.cm.sig (Af I.F)) (I.fmat γ.2) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat γ.2 =
        I.J.map (inclE (F := I.F) (Af I.F)) := γ.2.2
    obtain ⟨s1, s2⟩ := span_map_mulVec (inclE (F := I.F) (Af I.F)) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ hmf
    · exact hform_mulVec_mulVec _ _ _ hU
    · rw [hfin]; exact s1
    · rw [hfin]; exact s2

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
section
noncomputable section

namespace GlobalTheory.BridgeDict

open NumberField Matrix Formalism.MainNotions.S
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Ainf HA fstA sndA inclR)

theorem comp_eq_thetaV (I : AutInst) (v : InfinitePlace I.F) (θ : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ) :
    θ.comp (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)).toRingHom =
      Formalism.L2.SG.AdBridge.thetaV I v := by
  have key : (fun a : Ainf I.F => θ (a ⊗ₜ[I.F] (1 : I.E))) =
      fun a : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (a v) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hθ.2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)) ?_
    funext x
    have e : (algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E) =
        (1 : Ainf I.F) ⊗ₜ[I.F] (algebraMap I.F I.E x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    simp only [Function.comp_apply]
    rw [e, hθ.1, I.φ_over]
    exact (Formalism.L2.SG.AdBridge.evV_algebraMap I v x).symm
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul]
    have e : (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) (a ⊗ₜ[I.F] x) =
        (a.1 ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [e, map_mul, hθ.1, congrFun key a.1]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem tauF_apply (I : AutInst) (z : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I z =
      Algebra.TensorProduct.comm I.F _ _ (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fin_eq (I : AutInst) (h : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I h).map (Formalism.L2.SG.AdBridge.tauF I) =
      (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
  unfold Formalism.MainNotions.StandardLattice.finMat
  rw [Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  rw [tauF_apply]

theorem infMat_bridge (I : AutInst) (e : I.GA ≃ₜ* Formalism.L2.SG.AdBridge.HAd I) (he : Formalism.L2.SG.AdBridge.IsBridge I e)
    (v : InfinitePlace I.F) (θv : Ainf I.F ⊗[I.F] I.E →+* ℂ) (hθv : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θv) (x : I.GA) :
    Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θv (e x) = I.P v * uMat (x.1 v) * (I.P v)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [(he x).1 v, Formalism.L2.SG.AdBridge.ofHAInf, ← comp_eq_thetaV I v θv hθv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_map]
  rfl

end GlobalTheory.BridgeDict

namespace GlobalTheory.BridgeDict

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem bridge_dict : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  intro D θ hθ V fr
  have hb := Formalism.IndefR.Eqv.UI.brg_isBridge fr
  have hθv : ∀ v : InfinitePlace D.host.F,
      IsInfEmb (Formalism.IndefR.Eqv.UI.phiV D v) (θ ((Formalism.L2.Host.tauPl D).symm v)) := fun v => hθ _
  refine ⟨fun x => ?_, fun x τ A hA => ?_, fun W hW => ?_⟩
  · have h1 := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.Eqv.UI.instV fr)).2.1 (Formalism.IndefR.Eqv.UI.brg fr) hb
    have e : Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔
        Formalism.IndefR.Eqv.UI.brg fr x ∈ Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := Iff.rfl
    rw [e, ← h1]
    exact (Formalism.IndefR.Eqv.UI.brg fr).injective.mem_set_image
  · subst hA
    have h := infMat_bridge (Formalism.IndefR.Eqv.UI.instV fr) _ hb (Formalism.L2.Host.tauPl D τ) (θ τ)
      (by have h := hθv (Formalism.L2.Host.tauPl D τ); rwa [Equiv.symm_apply_apply] at h) x
    exact h
  · obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.CuspCompare.isIsot_iff (Formalism.IndefR.Eqv.UI.instV fr) W).1 hW
    refine ⟨r, C, hC, fun x hx => ?_⟩
    obtain ⟨L, R, hL, hR⟩ := GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E)
      (Formalism.IndefR.Eqv.UI.instV fr).J_det hC.2.1
    let T : GA D V ≃* (Formalism.IndefR.Eqv.UI.instV fr).GA := (Formalism.IndefR.Eqv.UI.brg fr).symm.toMulEquiv
    have hT : ∀ g, Formalism.IndefR.Eqv.UI.brg fr (T g) = g := fun g => (Formalism.IndefR.Eqv.UI.brg fr).apply_symm_apply g
    unfold NI at hx
    have := (GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (_root_.GlobalTheory.UnipApprox.strong_approximation _ _ hW).1 (fun g => ?_) _).1 hx
    · exact ((Formalism.IndefR.Eqv.UI.brg fr).symm_apply_apply x) ▸ this
    · rw [GlobalTheory.CuspCompare.mem_NA_iff (Formalism.IndefR.Eqv.UI.instV fr) _ hθv g (T g) ?_ ?_ hL hR]
      · exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)
      · rw [(hb (T g)).2, Formalism.L2.SG.AdBridge.ofHAFin, fin_eq]
        exact congrArg (fun h => (finMat _ _ h).map _) (hT g)
      · intro v
        rw [← infMat_bridge _ _ hb v _ (hθv v) (T g)]
        exact congrArg (infMat _ _ _) (hT g)

end GlobalTheory.BridgeDict
end
end

