module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanMultilinearValuesStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parIndep : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  have hlat := (_root_.GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D c hc j hj s hs).2
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine _root_.GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      have h1 := (hpar i.1).2 v i.2
      unfold ParFun at h1
      exact (hlat _ _).1 h1
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
        exact Finset.sum_congr rfl (fun i _ => (map_mul (starRingEnd ℂ) _ _).symm)
    · intro i _ hne h0
      apply hne
      simp [h0]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.PetCoef

theorem pet_smul_left {D : D7} (s : PiLocalization₂ D) (a : ℂ) (f g : GA D s.V → ℂ) :
    s.pet (a • f) g = a * s.pet f g := by
  unfold PiLocalization₂.pet Lift.pet
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul a _

theorem petco : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs ipD ip hM u v b κ hκ
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.T.multiplicitySpace_equivariant_real_points D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
  rw [key, pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

end GlobalTheory.ChainOnto.PetCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

section Frame

variable {n p q : ℕ} (e : Fin n ≃ Fin p ⊕ Fin q)

theorem submatrix_symm_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e.symm id * Y = (X * Y).submatrix e.symm id := by
  ext i j
  simp [Matrix.mul_apply]

theorem mul_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    B * X.submatrix e.symm id = (B.submatrix e e * X).submatrix e.symm id := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by ext; simp
  conv_lhs => rw [hB]
  rw [show X.submatrix e.symm id = X.submatrix e.symm (Equiv.refl _) from rfl, submatrix_mul_equiv]
  rfl

theorem conj_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (X.submatrix e.symm id)ᴴ * B * X.submatrix e.symm id = Xᴴ * B.submatrix e e * X := by
  rw [Matrix.mul_assoc, mul_submatrix_symm, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, Matrix.mul_assoc]

end Frame

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem sortedFrame_gram (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (sortedFrame M hV τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ = gramAt D V τ := by
  rw [sortedFrame, conj_submatrix_symm, Jpq_submatrix, M.fr_gram τ]

theorem isCartanFrame_sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Cusp.IsCartanFrame V (sortedFrame M hV) :=
  sortedFrame_gram M hV

theorem sortedFrame_cart (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    sortedFrame M hV τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ := by
  rw [sortedFrame, submatrix_symm_mul, mul_submatrix_symm, Jpq_submatrix, cart, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.one_mul]

theorem isCartanInv_cart (M : DSModel V S) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hd := fr_det M τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Formalism.REAL.Jm, diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp
  have hJh : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.REAL.Jm, diagonal_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, diagonal_apply, h, Ne.symm h]
  have hg : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have e : cart M τ = (M.fr τ)⁻¹ * ((M.fr τ)⁻¹)ᴴ * gramAt D V τ := by
    rw [cart, ← M.fr_gram τ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (M.fr τ)⁻¹ ((M.fr τ)⁻¹)ᴴ (M.fr τ)ᴴ, h1, Matrix.mul_one]
  rw [e]
  exact GlobalTheory.Doubling.isCartanInv_of_frame (Matrix.nonsing_inv_mul _ hd) hg hJ hJh

theorem exists_maj_cart (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) :
    ∃ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a ∧
      ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨a, ha, -, hs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ (fun τ => isCartanInv_cart M τ)
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D V τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D V τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

theorem exists_kStable (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊥, inferInstance, zero_mem _, fun g _ v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    obtain ⟨W', h1', h2', h3'⟩ := hy
    refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup h2 h2', fun g hg v hv => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg y hy) (h3' g hg z hz)
  | smul a x _ hx =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    exact ⟨W, h1, W.smul_mem a h2, h3⟩

theorem isKFinite_value (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf θ V (sortedFrame M hV)) (T v) := by
  choose W hWf hvW hWK using fun τ => exists_kStable M τ (hv τ)
  let W' : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => (W τ).comap (M.sm τ).subtype
  have hW' : ∀ τ, FiniteDimensional ℂ (W' τ) := fun τ => by
    haveI := hWf τ
    refine Module.Finite.of_injective (LinearMap.codRestrict (W τ) ((M.sm τ).subtype.comp (W' τ).subtype)
      fun x => x.2) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W τ => (z : M.H τ)) h))
  have hfd := GlobalTheory.T.finiteDimensional_span_multilinear_values' (fun τ => M.sm τ) (GA D V → ℂ) T W' hW'
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfd, fun k hk => ?_⟩
  obtain ⟨v', hv', hx⟩ := _root_.GlobalTheory.RealPointMove.translate_eq_move D θ hθ V S M J χ T hT k (GlobalTheory.Cusp.Kinf_le hk) v
  have e : (fun g => T v (g * k)) = T v' := funext hx
  rw [e]
  refine Submodule.subset_span ⟨v', fun τ => ?_, rfl⟩
  show ((v' τ : M.sm τ) : M.H τ) ∈ W τ
  rw [hv' τ]
  exact hWK τ _ (_root_.GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf D θ V S M hV k hθ hk τ) _ (hvW τ)

theorem conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} (F : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hF : F ∈ MultT θ M J χ) (w : SmT M)
    (hw : w ∈ Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v}) :
    (fun g => conj (F w g)) ∈ GlobalTheory.Cusp.A0 θ V (sortedFrame M hV) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 hF)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    have e : F (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm F v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    have ha := hT.aut v
    refine GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ V _ ha,
      (GlobalTheory.Cusp.conj_mem_cuspCont ⟨ha.cont, ha.left, hT.cusp v⟩).2.2⟩, ?_⟩
    exact GlobalTheory.Mem.AutConj.finiteDimensional_span_star (isKFinite_value θ hθ M hV hT v hv)
      (by rintro f ⟨k, hk, rfl⟩; exact ⟨k, hk, funext fun g => by simp⟩)
  | zero =>
    convert zero_mem (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)) using 1
    funext g; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext g; simp
  | smul a x _ hx =>
    convert (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)).smul_mem (conj a) hx using 1
    funext g; simp

end GlobalTheory.ChainOnto.RealData

open GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨RealData.sortedFrame s.M hs.sigOK, a, RealData.isCartanFrame_sortedFrame _ _, fun τ => RealData.isCartanInv_cart _ τ,
    fun τ => RealData.sortedFrame_cart _ _ τ, ha, hmaj, fun u v hv => RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isParamVec_of_injective_equivariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : GlobalTheory.LFun.IsParamVec σ J L h ρ' (f x) B) : GlobalTheory.LFun.IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, GlobalTheory.LFun.IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, GlobalTheory.LFun.IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem thetaKO_om_apply {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g a : GA D S)
    (x a' : GA D T) (u : WO S T → ℂ) : thetaKO om g x (om (a, a') u) = thetaKO om (g * a) (x * a') u := by
  simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem thetaKO_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {u : WO S T → ℂ}
    (hu : IsThetaFunO ψ S T u) (γ : GA D S) (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) :
    thetaKO om (γ * g) x u = thetaKO om g x u := by
  have e : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  simp only [thetaKO, e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hu)

theorem thetaIntegral_param : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  intro hP D hT ψ θ S T χS χT om hθ hW t ht ν 𝓕 hν h𝓕 v hunr w h f hf y B hy hc hB hne
  let U : Submodule ℂ (WO S T → ℂ) := by
    exact {
    carrier := {f | IsThetaFunO ψ S T f}
    add_mem' {f g} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) := by
      have h : IsThetaFunO ψ S T (f + g) := {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          obtain ⟨V, hV, hfix'⟩ := hg.level
          refine ⟨U ⊓ V, hU.inter hV, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu.1 hfin) w
          have eg := congrFun (hfix' u hu.2 hfin) w
          unfold heisO at ef eg ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, ef, eg]
        cont := hf.cont.add hg.cont
        smooth k L hL hreal w := (hf.smooth k L hL hreal w).add (hg.smooth k L hL hreal w) }
      exact h
    zero_mem' := by
      have h : IsThetaFunO ψ S T 0 := {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const }
      exact h
    smul_mem' c f (hf : IsThetaFunO ψ S T f) := by
      have h : IsThetaFunO ψ S T (c • f) := {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          refine ⟨U, hU, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu hfin) w
          unfold heisO at ef ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ef]
        cont := hf.cont.const_smul c
        smooth k L hL hreal w := contDiff_const.mul (hf.smooth k L hL hreal w) }
      exact h
    }
  have hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  let ρ0 : Representation ℂ (Gv S v) (GA D S → ℂ) := (rightReg ℂ (GA D S) ℂ).comp (embV S v)
  have hρ0 : ∀ a (z : GA D S → ℂ) g, ρ0 a z g = z (g * embV S v a) := fun _ _ _ => rfl
  let cy : GA D S → ℂ := fun g => conj (y g)
  let X : Submodule ℂ (GA D S → ℂ) := Submodule.span ℂ (Set.range fun a : Gv S v => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (Gv S v) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u, IsThetaFunO ψ S T u → ∀ x, IntegrableOn (fun g => thetaKO om g x u * z g) 𝓕 ν) ∧
      (∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u hu x => _root_.GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn hP D ψ S T χS χT om hW θ hθ ν 𝓕 hν h𝓕 u y hu hy hc (embV S v a) x,
        fun γ hγ g => ?_⟩
      show conj (y (γ * g * embV S v a)) = conj (y (g * embV S v a))
      rw [mul_assoc, hy.left γ hγ]
    | zero => exact ⟨fun u _ x => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (z + z') g) = fun g => thetaKO om g x u * z g + thetaKO om g x u * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u hu x).add (h2.1 u hu x)
    | smul c z _ h1 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (c • z) g) = fun g => c * (thetaKO om g x u * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u hu x).const_mul c
  let bf : U → X → GA D T → ℂ := fun u z x => ∫ g in 𝓕, thetaKO om g x (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D T → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z z.2).1 u' u'.2 x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z' z'.2).1 u u.2 x)]
      congr 1; funext g
      simp [mul_add])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ a a' (u : U) (z : X), b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a z) =
      (rightReg ℂ (GA D T) ℂ).comp (embV T v) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in 𝓕, thetaKO om g x (om (embV S v a, embV T v a') u) * (z : GA D S → ℂ) (g * embV S v a) ∂ν =
      ∫ g in 𝓕, thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
    simp_rw [thetaKO_om_apply]
    exact _root_.GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S ν 𝓕 hν h𝓕 (fun g => thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hW u.2 γ hγ, (hXp z z.2).2 γ hγ]) (embV S v a)
  have hx : GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ ⟨cy, hcy⟩ B :=
    isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective hB
  exact hT ψ S T χS χT om hW t ht v trivial hunr w h U hU ⟨f, hf.1⟩ hf X ρ ⟨cy, hcy⟩ B hx (GA D T → ℂ)
    ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) b hb hne

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
open GlobalTheory.Size
namespace GlobalTheory.Core.Rk.ThetaGrowthBoth

theorem thetaKO_modGrowth₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.Grow.ModGrowth₂ S T fun g h => thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, -, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  exact ⟨C * (sobO ψ θ μ 𝓕 d f).toReal, A, fun g h => (hC χS χT om hω μ 𝓕 hμ f hl).2 g h⟩

end GlobalTheory.Core.Rk.ThetaGrowthBoth

end
end

