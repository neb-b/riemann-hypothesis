module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodinger
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem submatrix_mul_id {R : Type} [CommRing R] {m n p k : ℕ} (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin p) R)
    (e : Fin k → Fin m) : (M * N).submatrix e id = M.submatrix e id * N := by
  ext i j
  simp [Matrix.mul_apply]

theorem actE_eq_of_conj_related {R : Type} [CommRing R] {n m k : ℕ} (e : Fin k ≃ Fin m) (P : Matrix (Fin n) (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin m) R) (G H : Matrix (Fin n) (Fin n) R)
    (M₁ : Matrix (Fin k) (Fin k) R) (Lx : Matrix (Fin k) (Fin n) R) (M₂ : Matrix (Fin n) (Fin n) R)
    (hLx : Lx = xᵀ.submatrix e id * G) (h₁ : M₁ = Qᵀ.submatrix e e) (h₂ : M₂ = H) (hu : Pᵀ * G = G * H) :
    ((P * x * Q)ᵀ.submatrix e id) * G = M₁ * Lx * M₂ := by
  subst hLx h₁ h₂
  rw [Matrix.transpose_mul, Matrix.transpose_mul, submatrix_mul_id, ← Matrix.mul_assoc (Qᵀ.submatrix e e),
    Matrix.submatrix_mul_equiv, submatrix_mul_id]
  simp only [Matrix.mul_assoc]
  rw [hu]

theorem unit_aux {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (P P' K G : Matrix (Fin n) (Fin n) R)
    (hPP : P * P' = 1) (hK : Kᵀ = -G) (h : (P.map c)ᵀ * K * P = K) : Pᵀ * G = G * P'.map c := by
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hK,
    Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h'
  have hc : P.map c * P'.map c = 1 := by
    rw [← Matrix.map_mul, hPP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc Pᵀ * G = Pᵀ * G * (P.map c * P'.map c) := by rw [hc, Matrix.mul_one]
    _ = (Pᵀ * G * P.map c) * P'.map c := by simp only [Matrix.mul_assoc]
    _ = G * P'.map c := by rw [h']

theorem eq_submatrix_symm {α : Type} {a b : ℕ} (f : Fin a ≃ Fin b) (M : Matrix (Fin b) (Fin b) α)
    (N : Matrix (Fin a) (Fin a) α) (h : M.submatrix f f = N) : M = N.submatrix f.symm f.symm := by
  subst h
  ext i j
  simp

theorem incM_neg_refl {D : D7} {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (-(G.submatrix (Equiv.refl (Fin n)) (Equiv.refl (Fin n)))) = -(G.map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.neg_apply, Matrix.submatrix_apply,
    Equiv.refl_apply, map_neg]

theorem neg_incM_eq {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : IsUnit J.det) {ξ : D.host.E} (hξ : ξ ≠ 0) :
    (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (ξ • (-ξ • J⁻¹)⁻¹) := by
  have e1 : (-ξ • J⁻¹)⁻¹ = (-ξ)⁻¹ • J := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ, inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul]
  have e2 : ξ • (-ξ)⁻¹ • J = -J := by
    rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
  rw [e1, e2]
  funext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]

theorem eq_map_conj {D : D7} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (AE D)) (h : Q = P.map (cA D)) : P = Q.map (cA D) := by
  subst h
  ext i j
  simp [Formalism.L2.Theta.cA_cA]

theorem eq_inv_transpose {R : Type} [CommRing R] {n : ℕ} (P P' B B' : Matrix (Fin n) (Fin n) R) (hP : P' * P = 1)
    (hB : B * B' = 1) (h : B = P'ᵀ) : P = B'ᵀ := by
  have h1 : Pᵀ * B = 1 := by rw [h, ← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have h2 : B' = Pᵀ := by
    calc B' = (Pᵀ * B) * B' := by rw [h1, Matrix.one_mul]
      _ = Pᵀ := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  rw [h2, Matrix.transpose_transpose]

theorem sgn_gram_eq {D : D7} (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε
  · show S.gram = _
    simp
  · show (neg S).gram = _
    rw [neg_gram]
    simp

theorem gram_neg_sgn {D : D7} (ε : Bool) (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (hJ : J = (if ε then 1 else -1 : D.host.E) • S.gram) : J = -(sgn ε S).gram := by
  rw [sgn_gram_eq, hJ]
  cases ε <;> simp

theorem gram_hspOf_transpose {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E)
    (h1 : (GlobalTheory.WeilSchrodinger.sesq D Jᵀ).IsSymm) h2 L hL h3 (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (GlobalTheory.WeilSchrodinger.hspOf D Jᵀ h1 h2 L hL h3 sg).gramᵀ = J := by
  rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
  exact Matrix.transpose_transpose J


set_option maxHeartbeats 1600000 in
theorem exists_weil_of_oriented : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep S X), IsWeil ψ ε S X χ χ' ω →
    ∃ om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws, M.IsWeil Bs.ψ χ χ' om ∧
      ∀ Φ f, IsDatum M ψ cS Φ f → ∀ g h,
        IsDatum M ψ cS (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g, kapX X e hJW h) Φ) (ω (g, h) f) := by
  intro D ψ θ _hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW _hcart M hM cS hcS χ χ' ω hω
  subst hψ
  have hω' : IsWeilDatumO Bs.ψ (sgn ε S) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D Bs hBs S.rank Vs r s hV
  obtain ⟨hJd, L0, hL0, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D Bs hBs d Ws r' s' hW
  let Th := GlobalTheory.WeilSchrodinger.hspOf D Vs.Jᵀ h1 h2 Vs.L hV.lat.toIsLattice h3 (fun _ => (r, s))
  let Sh := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Ws.J⁻¹) h4 h5 L0 hL0 h6 (fun _ => (s', r'))
  have hTt : Th.gramᵀ = Vs.J := gram_hspOf_transpose _ _ _ _ _ _ _
  have hSg : Sh.gram = -D.host.xi0 • Ws.J⁻¹ := GlobalTheory.WeilSchrodinger.gram_hspOf _ _ _ _ _ _ _
  have hdX : X.rank = d := Fin.equiv_iff_eq.mp ⟨e⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

  have hT' : Th.gramᵀ = -((sgn ε S).gram.submatrix (Equiv.refl (Fin S.rank)) (Equiv.refl (Fin S.rank))) := by
    rw [hTt, Equiv.coe_refl, Matrix.submatrix_id_id]
    exact gram_neg_sgn ε S hJ
  have hS' : Sh.gram⁻¹ = -(X.gramᵀ.submatrix e.symm e.symm) := by
    refine Matrix.inv_eq_left_inv ?_
    have hK : D.host.xi0 • X.gramᵀ.submatrix e.symm e.symm = Ws.J := by rw [hJW]; rfl
    have key : (-(X.gramᵀ.submatrix e.symm e.symm)) * (-D.host.xi0 • Ws.J⁻¹) = 1 := by
      rw [neg_mul, Matrix.mul_smul, neg_smul, neg_neg, ← Matrix.smul_mul, hK]
      exact Matrix.mul_nonsing_inv _ hJd
    rw [hSg]
    exact key

  obtain ⟨φ', hφ'c, hφ'Q, hφ'm, hφ'S, hφ'd⟩ := _root_.GlobalTheory.GrpConj.exists_conj_equiv D (sgn ε S) Th (Equiv.refl _) hT'
  obtain ⟨φ, hφc, hφQ, hφm, hφS, hφd⟩ := _root_.GlobalTheory.InvTransposeIso.grp_contra D X Sh e.symm hS'
  obtain ⟨L, hL1, -, hLc, hLc', hLQ, hLi, hLf⟩ := _root_.GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D (sgn ε S) X Sh Th (Equiv.refl _) e.symm
  have hsy := _root_.GlobalTheory.DarbouxSymp.symplO_darboux D (sgn ε S) X Sh Th (Equiv.refl _) e.symm hT' hS'
  have hLx : ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), L u = (HMul.hMul (uᵀ.submatrix e id) ((sgn ε S).gram.map (incA D)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun u => (hL1 u).trans rfl
  have hcL : ∀ u, cS u = L u := fun u => by
    rw [hcS, hLx, sgn_gram_eq]
    rfl

  have hact : ∀ (g : GA D Sh) (h : GA D Th) (x : WO Sh Th), L (actO Sh Th g h x) = actO (sgn ε S) X (φ' h) (φ g) (L x) := by
    intro g h x
    have hg : Formalism.L2.Theta.mt X (φ g) = ((Formalism.L2.Theta.mt Sh g⁻¹)ᵀ).submatrix e e :=
      eq_submatrix_symm e.symm _ _ (hφm g)
    have hh : Formalism.L2.Theta.mt (sgn ε S) (φ' h)⁻¹ = (Formalism.L2.Theta.mt Th h⁻¹).map (cA D) := by
      rw [← map_inv]
      exact hφ'm h⁻¹
    have hTinc : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = -((sgn ε S).gram.map (incA D)) := by
      have e0 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gramᵀ := rfl
      rw [e0, hT']
      exact incM_neg_refl _
    have hPP : Formalism.L2.Theta.mt Th h * Formalism.L2.Theta.mt Th h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
    have hu := unit_aux (cA D) _ _ _ _ hPP hTinc (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram Th h)
    exact (hLx _).trans (actE_eq_of_conj_related e _ x _ _ _ _ _ _ (hLx x) hg hh hu)

  obtain ⟨ω', hω'', hrel⟩ := _root_.GlobalTheory.SwapWeil.isWeilDatumO_swap D Bs.ψ (sgn ε S) X Sh Th hdX.symm rfl L φ.toMonoidHom φ'.toMonoidHom hLc hLc' hLQ
    (fun x y => by rw [hL1, hL1]; exact hsy x y) hLi hLf hφc hφ'c hφQ hφ'Q hact hφS hφ'S hφd hφ'd χ χ' (ω.toSgn ε) hω'
  have hA : Vs.J = Th.gramᵀ := hTt.symm
  have hB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • Sh.gram⁻¹) := by
    rw [hSg]
    exact neg_incM_eq Ws.J hJd hξ
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.ThetaTransform.exists_isTransport D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω''
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h3 := _root_.GlobalTheory.WeilAdm.transport_adm D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h4 := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h5 := _root_.GlobalTheory.WeilCont.continuous_transport D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h6 := _root_.GlobalTheory.DblSchr.doubledModel D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h7 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) Bs.ψ M.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hW : M.IsWeil Bs.ψ χ χ' om :=
    ⟨⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩, ⟨GlobalTheory.WeilSchrodinger.transD _ M.co, GlobalTheory.WeilSchrodinger.transD_e M.co,
      GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
  refine ⟨om, hW, ?_⟩

  intro Φ f hΦ g h
  have hm : Formalism.L2.Theta.mt (sgn ε S) ((ofSgn ε S).symm g) = Formalism.L2.Theta.mt S g := by
    rw [← mt_ofSgn, MulEquiv.apply_symm_apply]
  have h0 := hφ'm (φ'.symm ((ofSgn ε S).symm g))
  rw [MulEquiv.apply_symm_apply] at h0
  have ha : Formalism.L2.Theta.mt Th (φ'.symm ((ofSgn ε S).symm g)) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g).1.1 :=
    eq_map_conj _ _ (hm.symm.trans h0)
  have h1 := hφm (φ.symm h)
  rw [MulEquiv.apply_symm_apply] at h1
  have hP : Formalism.L2.Theta.mt Sh (φ.symm h)⁻¹ * Formalism.L2.Theta.mt Sh (φ.symm h) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]
  have hb : Formalism.L2.Theta.mt Sh (φ.symm h) = ((kapX X e hJW h)⁻¹).1.1ᵀ :=
    eq_inv_transpose _ _ _ _ hP (Units.mul_inv (kapX X e hJW h).1) h1
  obtain ⟨hs, ht⟩ := hom (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g) (kapX X e hJW h) (φ.symm h) (φ'.symm ((ofSgn ε S).symm g))
    ha hb Φ hΦ.1
  refine ⟨hs, fun u => ?_⟩
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F M.co Bs.ψ Φ = fun u => f (L u) := funext fun u => by
    rw [← hcL]
    exact hΦ.2 u
  have k1 := congrFun ht u
  have k2 := congrArg (fun F => ω' (φ.symm h, φ'.symm ((ofSgn ε S).symm g)) F u) hΦf
  have k3 := congrFun (hrel (φ.symm h) (φ'.symm ((ofSgn ε S).symm g)) f) u
  rw [hcL]
  refine k1.trans (k2.trans (k3.trans ?_))
  simp [WRep.toSgn]

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIdeleModulusConjLevelDetEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem val_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 :=
  le_antisymm ha (by
    calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ a := mul_le_of_le_one_right' hb)

theorem valued_isInt {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v}
    (h : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x) : Valued.v x ≤ 1 := by
  obtain ⟨o, rfl⟩ := h
  exact o.2

theorem chart_val_eq_one {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart es v π) {c c' : AE D} (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : Valued.v (π c) = 1 := by
  obtain ⟨φ, hφ, hint, -⟩ := GlobalTheory.ChartLevels.chart_levels D es PP v π he hπ
  have hc' : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c')) = 1 := by
    have h1 : GlobalTheory.StdFrames.cpt PP (toEAf D c) * GlobalTheory.StdFrames.cpt PP (toEAf D c') = 1 := by
      rw [← map_mul, ← map_mul, hcc, map_one, map_one]
    have h2 := congrArg Valued.v h1
    rw [map_mul, hc, one_mul, map_one] at h2
    exact h2
  have key : ∀ y : AE D, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D y)) = 1 → Valued.v (π y) ≤ 1 := by
    intro y hy
    rw [← hφ]
    refine valued_isInt ((hint _).1 ((GlobalTheory.AdIsom.mem_OA _).2 fun Q => ?_))
    rw [map_mul]
    by_cases hQ : Q = PP
    · subst hQ; rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul, hy]
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, map_zero]; exact zero_le'
  refine val_eq_one_of_le (key c hc) (key c' hc') ?_
  rw [← map_mul, ← map_mul, hcc, map_one, map_one]

theorem absFin_single {es : AE D} {PP : Pl D.host.E} (he : IsIdemAt es PP) (u : (AE D)ˣ) (c : AE D)
    (hu : (u : AE D) = es * c + (1 - es)) (c' : AE D) (hcc : c * c' = 1)
    (hc : Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart es he.1
  have hee : es * es = es := he.1.1
  have hu1 : (1 - es) * (u : AE D) = 1 - es := by rw [hu]; linear_combination (1 - c) * hee
  rw [GlobalTheory.SplitLinear.absFin_split D es v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hπu : π (u : AE D) = π c := by
    rw [hu, map_add (f := _), map_mul, map_sub, map_one, hπ.map_e hee, one_mul, sub_self, add_zero]
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v (π (u : AE D)))) = 1
  rw [hπu, chart_val_eq_one he hπ hcc hc, WithZero.log_one, zpow_zero]

theorem absFin_idemSum_eq_one {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (x : (AE D)ˣ) (c c' : AE D)
    (hcc : c * c' = 1) (hx : (x : AE D) = e * c + (1 - e))
    (hc : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D c)) = 1) : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = 1 := by
  obtain ⟨⟨es, hes, hae⟩, -⟩ := he
  let u : {PP // PP ∈ P} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * c + (1 - es PP.1)
      inv := es PP.1 * c' + (1 - es PP.1)
      val_inv := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := GlobalTheory.SplitIdeleModulus.unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P.attach, (fun PP => es PP * c + (1 - es PP)) PP.1
    rw [Finset.prod_attach P (fun PP => es PP * c + (1 - es PP)),
      GlobalTheory.SplitIdeleModulus.prod_idem hes _ P subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, GlobalTheory.SplitIdeleModulus.absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod]
  exact Finset.prod_eq_one fun PP _ => absFin_single (hes PP.1 PP.2) (u PP) c rfl c' hcc (hc PP.1 PP.2)

end GlobalTheory.DetIdeleUnit

open GlobalTheory.FunObj in
theorem GlobalTheory.DetIdeleUnit.cpt_gdet_kapAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
  ((gdet (GlobalTheory.TopLevelInv.kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) = GlobalTheory.StdFrames.cpt w ((finG (G.V (.top (j + 1))) k).val.det) := by
  have hu : IsUnit ((S.βp (j + 1)).val.det) := (Matrix.GeneralLinearGroup.det (S.βp (j + 1))).isUnit
  have ha : ((S.βp (j + 1)).val.map (GlobalTheory.StdFrames.cpt w)).det ≠ 0 := by
    intro h0; apply (hu.map (GlobalTheory.StdFrames.cpt w)).ne_zero; rw [RingHom.map_det]; exact h0
  unfold GlobalTheory.TopLevelInv.kapAt inBasis
  simp [gdet, GlobalTheory.StepData.reGL, Matrix.GeneralLinearGroup.det, GlobalTheory.StdFrames.loc, RingHom.map_det]
  rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]

theorem GlobalTheory.DetIdeleUnit.valued_eq_one_of_valuation {D : D7} {w : Pl D.host.E} (y : Kw w) (h : ValuativeRel.valuation (Kw w) y = 1) : Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  first
  | exact e.eq_one_iff_eq_one.1 h
  | exact le_antisymm (e.le_one_iff_le_one.1 h.le) (e.one_le_iff_one_le.1 h.ge)

namespace GlobalTheory.DetIdeleUnit

open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem det_mt_conj (V : HSp D) (h k : GA D V) :
    (Formalism.L2.Theta.mt V (h⁻¹ * k * h)).det = (Formalism.L2.Theta.mt V k).det := by
  rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, Matrix.det_mul, Matrix.det_mul,
    mul_comm (Formalism.L2.Theta.mt V h⁻¹).det, mul_assoc, ← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel,
    GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, mul_one]

theorem cpt_det_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P)
    (V : HSp D) (g : GA D V) :
    GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det) =
      GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det) := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc0 : e * cA D e = 0 := he.2
  obtain ⟨hf1, hf2⟩ := idem_conj_sum hee hc0
  obtain ⟨⟨es, hes, hae⟩, -⟩ := id he
  let ψ : AE D →+* Kw PP := (GlobalTheory.StdFrames.cpt PP).comp (toEAf D)
  have hψe : ψ e = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hae, map_sum, Finset.sum_eq_single PP]
    · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · intro Q hQ hne
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).2 PP (Ne.symm hne)
    · intro h; exact absurd hPP h
  have hψc : ψ (cA D e) = 0 := by
    have := congrArg ψ hc0
    rwa [map_mul, hψe, one_mul, map_zero] at this
  have hψa : ψ (e + cA D e) = 1 := by rw [map_add (f := _), hψe, hψc, add_zero]
  show ψ _ = ψ _
  rw [RingHom.map_det, RingHom.map_det, mt_cutPart hf1 hf2]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
    map_mul, map_sub, map_one, hψa, hψe, hψc, one_mul, sub_self, zero_mul, add_zero]

theorem absFin_detAt_cutPart {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hee : e * e = e) (V : HSp D)
    (g : GA D V) (hg : ∀ PP ∈ P, Valued.v (GlobalTheory.StdFrames.cpt PP (toEAf D (Formalism.L2.Theta.mt V g).det)) = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g)) = 1 :=
  absFin_idemSum_eq_one he _ (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det
    (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)⁻¹).det
    (by rw [← Matrix.det_mul, ← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]) rfl
    (fun PP hPP => by rw [cpt_det_cutPart he hPP]; exact hg PP hPP)

end GlobalTheory.DetIdeleUnit


open GlobalTheory.DetIdeleUnit in
theorem GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  intro D T L sc G W U S t μ₀ hμ ht Φ β j hj k hk e he
  refine absFin_detAt_cutPart he _ _ _ fun PP hPP => ?_
  have h1 := GlobalTheory.TopLevelInv.valuation_gdet_kapAt S hj hk ⟨PP, hPP⟩
  rw [cpt_gdet_kapAt] at h1
  have h2 := valued_eq_one_of_valuation _ h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, det_mt_conj]
  rw [RingHom.map_det]
  exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.TopLevelInv

theorem phase_eq_of_two_steps : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  intro k _ _ _ _ _ _ Γ j hA x x' e e' hx he h0 hrow hcol
  have hch : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 →
      ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by
    intro i h1 h2; rw [hx i h1 h2, he i h1 h2]
  have hcv : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → ∀ r, colVar x' e' i r = colVar x e i r := by
    intro i h1 h2 r; simp only [colVar]; rw [hx i h1 h2, he i h1 h2]
  have hrv : ∀ n : ℕ, n ≠ j → n ≠ j + 1 → ∀ s, rowVar x' e' n s = rowVar x e n s := by
    intro n h1 h2 s; unfold rowVar
    split_ifs with h
    · rw [hx n h1 h2, he ⟨n, h⟩ h1 h2]
    · rw [hx n h1 h2]
  have hodd : Even (Γ.m - 2 - (j + 1)) ↔ Odd (Γ.m - 2 - j) := by
    rw [show Γ.m - 2 - j = (Γ.m - 2 - (j + 1)) + 1 by omega, Nat.odd_add_one, Nat.not_odd_iff_even]
  have hP1 : (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x' e' (j + 1 + 1) r * colVar x' e' ⟨j + 1, by omega⟩ r else 0)
      = (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x e (j + 1 + 1) r * colVar x e ⟨j + 1, by omega⟩ r else 0) := by
    split_ifs with hE
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hrv (j + 1 + 1) (by omega) (by omega), hcol (hodd.1 hE) r]
    · rfl
  unfold phase
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add (⟨j, by omega⟩ : Fin (Γ.m - 1)) ⟨j + 1, by omega⟩ (by simp [Fin.ext_iff]) ?_]
  · have hch1 := h0
    simp only [Fin.val_mk] at hP1 ⊢
    rw [hP1]
    linear_combination -h0
  · rintro ⟨i, hi⟩ ⟨h1, h2⟩
    simp only [ne_eq, Fin.ext_iff, Fin.val_mk] at h1 h2
    rw [sub_eq_zero, hch ⟨i, hi⟩ h1 h2]
    congr 1
    by_cases hij : i + 1 = j
    · subst hij
      split_ifs with hE
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2, hrow ?_ r]
        rw [show Γ.m - 2 - i = (Γ.m - 2 - (i + 1)) + 1 by omega, Nat.even_add_one, Nat.not_even_iff_odd] at hE
        exact hE
      · rfl
    · split_ifs
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2 r, hrv (i + 1) hij (by omega) r]
      · rfl

end GlobalTheory.TopLevelInv
end

