module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Formalism.LocalToGlobal.Columns.ChainTopTilQK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.RatEntry

theorem unitV_det_red_one {X : Fields} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (χ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ)
    (k : GLint X.E n P) (hk : redGL n P k = 1) : LocE.unitV χ ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 :=
  tqk_unitV_one χ (by rw [(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one])

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem red_pass_one {u : Pr.Word} {j : ℕ} {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (g : UF X.E (R.N j)) (p : ChPt (R := R) sel mu u j) (κ : GLQ X.E (R.N j) (rowSG Pr sel mu))
    (hκ : ∀ P, frsF sel mu (((g, 1, 1) : FrmG Λ Θ) • p) P = g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) (P : rowSG Pr sel mu) :
    redGL (R.N j) P.1 (κ P) = 1 := by
  classical
  have h := hκ P
  by_cases hP : P.1 ∈ Pr.vGs
  · have e : κ P = passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩ := by
      apply Subtype.ext
      unfold frsF at h
      simp only [dif_pos hP] at h
      show (κ P).1 = ((((g, 1, 1) : FrmG Λ Θ) • p).deco.1.liftFr ⟨P.1, hP⟩)⁻¹ * g.1 * p.deco.1.liftFr ⟨P.1, hP⟩
      rw [h, Subgroup.coe_inv]
      group
    rw [e]
    exact redGL_passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩
  · unfold frsF at h
    simp only [dif_neg hP] at h
    have h1 : ((κ P)⁻¹).1 = 1 := by
      have h' : g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * ((κ P)⁻¹).1) =
          g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * 1) := by
        rw [← h]
        show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
        simp [mul_assoc]
      exact mul_left_cancel (mul_left_cancel h')
    have h2 : κ P = 1 := inv_eq_one.1 (Subtype.ext h1)
    rw [h2, map_one]

theorem rho_pass_one (i : ℕ) (κ : GLQ X.E (R.N i) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu))
    (hκ : ∀ P : rowSG Pr sel mu, redGL (R.N i) P.1 (κ P) = 1) (hκ' : ∀ P : rowSG Pr sel mu, redGL (R.N (i + 1)) P.1 (κ' P) = 1) :
    ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
      rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) = 1 := by
  refine Finset.prod_eq_one fun P _ => ?_
  have h1 : redGL _ P.1 ((κ P)⁻¹) = 1 := by rw [map_inv, hκ P, inv_one]
  have h2 : redGL _ P.1 ((κ' P)⁻¹) = 1 := by rw [map_inv, hκ' P, inv_one]
  rw [Pi.inv_apply, Pi.inv_apply]
  unfold rhoS rhoT
  rw [unitV_det_red_one _ ((κ P)⁻¹) h1, unitV_det_red_one _ ((κ' P)⁻¹) h2, mul_one]

theorem xiEntry_rat {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (g : UF X.E (R.N i)) (g' : UF X.E (R.N (i + 1))) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiEntry Ch sel mu cst L i al be
        (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p)
        (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p')
        (g'.1.toLinearMap ∘ₗ x ∘ₗ g.1.symm.toLinearMap) = XiEntry Ch sel mu cst L i al be p p' x := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have e1 : (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p) =
      ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) • p := rfl
  have e2 : (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p') =
      ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) • p' := rfl
  rw [e1, e2]
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) p'
  have key := GlobalTheory.MatLaw.xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  rw [rho_pass_one i κ κ' (red_pass_one g p κ hκ) (red_pass_one g' p' κ' hκ'), mul_one, ec, ec'] at key
  rw [key]
  simp

end GlobalTheory.RatEntry

namespace GlobalTheory.RatEntry

theorem xiPt_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _hT i hi hlt β β' x x' p p' _hp _hp' g g' w
  unfold xiPt
  rw [dif_pos hlt, dif_pos hlt]
  exact GlobalTheory.RatEntry.xiEntry_rat hP.fields.ok t.pr_ok hP.sel ⟨hP.avoid.2, hP.avoid.1⟩ (t.idx_ok μ) hlt _ _ g g' p p' w

end GlobalTheory.RatEntry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MtFiniteOrder
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TieFinOrd


set_option maxHeartbeats 4000000 in
theorem mt_finite_order : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → ∃ n : ℕ, 0 < n ∧ (t.O u μ).mt (i + 1) (dtU y) ^ n = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  set z := Matrix.GeneralLinearGroup.det y.1 with hz
  have hconj : conjId (sigD D) z = z⁻¹ := by
    have h1 : z * conjId (sigD D) z = 1 := hzU
    exact eq_inv_of_mul_eq_one_right h1
  have hh90 : h90 (sigD D) z = Matrix.GeneralLinearGroup.det (y * y).1 := by
    show z / conjId (sigD D) z = _
    rw [hconj, div_inv_eq_mul]
    show _ = Matrix.GeneralLinearGroup.det (y.1 * y.1)
    rw [map_mul]
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom z with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = z := by
    ext
    simp [x]
  have hq : A.q x = dtU (y * y) := H.q_dt x (y * y) (by rw [hxx, hh90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hint.1
    · simpa [x] using hint.2
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∃ n : ℕ, 0 < n ∧ D.muTil (i + 1) (A.q x) ^ n = 1 := by
    rw [H.muTil _ hiso ⟨i, hi⟩ (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    exact GlobalTheory.HeckeFin.finite_order _ _ _ (fun w => rfl) ((GlobalTheory.Mem.ReadEx.mem_intU_iff x).1 hxint)
  obtain ⟨n, hn, hmun⟩ := hmu
  have hsq : (t.O u μ).mt (i + 1) (dtU y) ^ 2 = (t.O u μ).mt (i + 1) (A.q x) := by
    rw [hq, map_mul, map_mul, sq]
  by_cases hμ : μ = D.what₂.mu0
  · refine ⟨2 * n, by omega, ?_⟩
    rw [pow_mul, hsq, (H.ref hμ).2]
    exact hmun
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    have htor := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at htor
    obtain ⟨k, hk, hkk⟩ := (isOfFinOrder_iff_pow_eq_one).1 htor.1.1.1.2
    refine ⟨2 * (n * k), by positivity, ?_⟩
    rw [pow_mul, hsq, hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, mul_pow, pow_mul, hmun, one_pow, one_mul,
      hξ x, ← map_pow, mul_comm, pow_mul]
    have : ((t.tup μ : Chr t.X.F t.X.E t.X.K) x) ^ k = 1 := by
      rw [← MonoidHom.pow_apply, hkk, MonoidHom.one_apply]
    rw [this, one_pow, map_one]

end GlobalTheory.TieFinOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

open scoped TensorProduct

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem coordRat_toLE_mul (g k : GL (Fin N) E) (v : Fin N → E) : toLE (g * k) v = toLE g (toLE k v) := by
  rw [toLE_apply, toLE_apply, toLE_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem coordRat_toLE_inv_apply (g : GL (Fin N) E) (v : Fin N → E) : toLE g⁻¹ (toLE g v) = v := by
  rw [← coordRat_toLE_mul, inv_mul_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_apply_inv (g : GL (Fin N) E) (v : Fin N → E) : toLE g (toLE g⁻¹ v) = v := by
  rw [← coordRat_toLE_mul, mul_inv_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_symm (g : GL (Fin N) E) (v : Fin N → E) : (toLE g).symm v = toLE g⁻¹ v := by
  apply (toLE g).injective
  rw [LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]

theorem coordRat_inFr {a b : ℕ} (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (co γ : GL (Fin a) E) (co' γ' : GL (Fin b) E) (z : (Fin a → E) →ₗ[E] (Fin b → E)) (v : Fin a → E) :
    inFr (toStdCo σ J co) (toStdCo σ J' co') (inFr (stdG σ J γ) (stdG σ J' γ') z) v =
      toLE (co' * γ' * co'⁻¹)⁻¹ (inFr (toStdCo σ J co) (toStdCo σ J' co') z (toLE (co * γ * co⁻¹) v)) := by
  simp only [inFr, toStdCo, stdG, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, coordRat_toLE_symm, LinearEquiv.symm_apply_apply,
    _root_.mul_inv_rev, inv_inv, coordRat_toLE_mul, coordRat_toLE_inv_apply, coordRat_toLE_apply_inv]

end Alg

theorem seamHom_inFr_stdG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E) (γ' : GL (Fin (D.R.N (i + 1))) D.host.E)
      (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))),
      seamGL t.seam g.1 = A.crd i (Nat.le_of_succ_le hi) * γ * (A.crd i (Nat.le_of_succ_le hi))⁻¹ →
      seamGL t.seam g'.1 = A.crd (i + 1) hi * γ' * (A.crd (i + 1) hi)⁻¹ → ∀ z : HomE D.host.E (D.R.N i) (D.R.N (i + 1)),
      seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) =
      g'.1.toLinearMap ∘ₗ seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) ∘ₗ g.1.symm.toLinearMap) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi γ γ' g g' hg hg' z
  have hS : ∀ {p q : ℕ} (x : HomE D.host.E p q) (w : Sp t.X.E p),
      (fun l => t.seam.iE (seamHom t.seam x w l)) = x (fun k => t.seam.iE (w k)) :=
    fun x w => funext (seamHom_apply t.seam x w)
  have hG : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h v l)) = toLE (seamGL t.seam h) (fun l => t.seam.iE (v l)) := by
    intro n h v
    rw [toLE_apply, seamGL_mulVec]
  have hw : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h.symm v l)) = toLE (seamGL t.seam h)⁻¹ (fun l => t.seam.iE (v l)) := by
    intro n h v
    apply (toLE (seamGL t.seam h)).injective
    rw [← hG, LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]
  refine LinearMap.ext fun w => funext fun l => ?_
  have key : (fun l => t.seam.iE (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) w l)) =
      (fun l => t.seam.iE (g'.1 (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) (g.1.symm w)) l)) := by
    rw [hG, hS, hS, hw, hg, hg', coordRat_inFr, coordRat_toLE_apply_inv, coordRat_toLE_apply_inv]
  exact t.seam.iE.injective (congrFun key l)

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentPullbackLatticeVectorMemDualSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.AwayLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem prV_pullV_mem_latS_dual : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  have hmono : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))
  apply hmono
  induction hl using Submodule.span_induction with
  | mem y hy => exact Formalism.L2.Geo.Def.PN.prV_latS lev.Lb v hy
  | zero =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) k)) = 0 := by
      ext k
      have h0 : pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) = 0 := by
        have := pullV_add (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) 0
        funext j
        have hj := this j
        rw [add_zero] at hj
        simpa using hj
      rw [h0, Pi.zero_apply, map_zero, Pi.zero_apply]
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (a + b) k)) =
        (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) +
          (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 b k)) := by
      ext k
      rw [Pi.add_apply, pullV_add, map_add (f := _)]
    rw [this]; exact add_mem ha hb
  | smul c a _ ha =>
    have hc : inclE (F := D.host.F) (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.E) D.host.E c) ∈ intV D.host.E v :=
      Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 D.host.E) D.host.E c, ⟨c, rfl⟩⟩, rfl⟩)
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (c • a) k)) =
        (⟨_, hc⟩ : intV D.host.E v) • (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) := by
      ext k
      rw [pullV_osmul, map_mul]
      rfl
    rw [this]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.AwayLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwLatRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem seam_lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) : s.lat (Formalism.HermitianLatticesTheory.gmap g N) = mvL (seamGL s g) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  unfold mvL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formalism.L2.Col.mem_gmap] at hx
    refine ⟨s.vec (g.symm x), (s.mem_lat N _).2 ⟨_, hx, rfl⟩, ?_⟩
    show (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (g.symm x l)) = fun l => s.iE (x l)
    rw [seamGL_mulVec, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    refine ⟨g x0, ?_, ?_⟩
    · rw [Formalism.L2.Col.mem_gmap, LinearEquiv.symm_apply_apply]; exact hx0
    · show (fun l => s.iE (g x0 l)) = (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x0 l))
      rw [seamGL_mulVec]


set_option maxHeartbeats 1000000 in
theorem lat_moved : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a _ _ i hi β x x₁ γ hγ hx g hg p hp
  have e1 : ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
  rw [e1, seam_lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]

end GlobalTheory.TwLatRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphism
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.SeamExp

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conjP_seamP {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    conjPrime₂ (seamP s P) = seamP s (conjPrime₂ P) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
  rw [mem_conjP, mem_seamP, mem_conjP]
  have h : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) := by
    apply RingOfIntegers.ext
    show star (s.iE (x : X.E)) = s.iE (star (x : X.E))
    rw [hs.2, star_eq_conj]
  rw [h, mem_seamP]

theorem expS_seam : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  intro D X s hs SS P
  have hm : ∀ Q, seamP s Q ∈ SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding ↔ Q ∈ SS :=
    fun Q => Finset.mem_map' _
  have h1 := hm P
  have h2 := hm (conjPrime₂ P)
  rw [← conjP_seamP s hs] at h2
  unfold expS
  by_cases hP : P ∈ SS
  · rw [if_pos (h1.2 hP), if_pos hP]
  · rw [if_neg (fun h => hP (h1.1 h)), if_neg hP]
    by_cases hQ : conjPrime₂ P ∈ SS
    · rw [if_pos (h2.2 hQ), if_pos hQ]
    · rw [if_neg (fun h => hQ (h2.1 h)), if_neg hQ]

end GlobalTheory.TwU.SeamExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem unit_hform_mulVec (σ : E →+* E) (J B : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J (B *ᵥ x) (B *ᵥ y) = hform σ (cT σ B * J * B) x y := by
  have key : ∀ (K : Matrix (Fin N) (Fin N) E) (v w : Fin N → E), hform σ K v w = (σ ∘ v) ⬝ᵥ (K *ᵥ w) := by
    intro K v w
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h1 : σ ∘ (B *ᵥ x) = (B.map σ) *ᵥ (σ ∘ x) := funext fun l => RingHom.map_mulVec σ B x l
  rw [key, key, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ x), cT,
    Matrix.vecMul_transpose]

theorem unit_hform_one (σ : E →+* E) (x y : Fin N → E) : hform σ 1 x y = ∑ a, σ (x a) * y a := by
  simp [hform, Matrix.one_apply]

theorem cT_mul_self_of_hform (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E)
    (h : ∀ x y, hform σ 1 (M *ᵥ x) (M *ᵥ y) = hform σ 1 x y) : cT σ M * M = 1 := by
  ext p q
  have h1 := h (Pi.single p 1) (Pi.single q 1)
  rw [unit_hform_mulVec, Matrix.mul_one] at h1
  simpa [hform, Pi.single_apply, apply_ite σ] using h1

end Gen

section Gen2

variable {E : Type} [Field E] {N : ℕ}

theorem cT_mul_self_toStdCo_stdG (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = J) (hγ : γ ∈ UJ σ J) :
    cT σ (LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap) *
      LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap = 1 := by
  have hc : IsOrthCo σ J (toLE co) := by
    intro x y
    have h := unit_hform_mulVec σ 1 co.1 x y
    rw [Matrix.mul_one, hco, unit_hform_one] at h
    exact h
  have hs : IsOrthCo σ J (stdCo σ J) := Classical.epsilon_spec (p := IsOrthCo σ J) ⟨_, hc⟩
  have hγ' : cT σ γ.1 * J * γ.1 = J := hγ
  apply cT_mul_self_of_hform
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, unit_hform_one, unit_hform_one]
  obtain ⟨x, rfl⟩ := (toLE co).surjective x
  obtain ⟨y, rfl⟩ := (toLE co).surjective y
  rw [hc]
  simp only [toStdCo, stdG, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hs]
  have h := unit_hform_mulVec σ J γ.1 x y
  rw [hγ'] at h
  exact h

end Gen2

theorem ratIsometry_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi γ hγ
  have h := cT_mul_self_toStdCo_stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi) γ (hP.crd_orth i hi) hγ
  rw [mul_eq_one_comm] at h
  exact h

end GlobalTheory.TwV

end
end

