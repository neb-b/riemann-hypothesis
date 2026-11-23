module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateStepPsiRationalRepEqColumnsDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NuRowZeroLeThreeMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRange

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

end GlobalTheory.CoreHt.RowsRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateStepPsiRationalRepEqColumnsDatumStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  obtain ⟨eg, hegO, hgv⟩ := hg
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
  have hegE : eg = E' := Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)
  subst hegE
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') :=
    PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'
  have hprod : toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) := by
    have h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : HomE X.E b a),
        toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι := by
      intro A B a b e e' z
      ext i j
      simp [toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rw [h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ E₁ E' E', Matrix.map_mul]
  have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E) := by
    have h := RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')
    rw [RingHom.mapMatrix_apply] at h
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h,
      Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1) := by
    rw [Fintype.card_congr E₁, Fintype.card_fin]
  have hPhi1 := hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)
  have char_scalar (a : X.E) (u : kˣ)
      (hu : (u : k) = ι a) (N : ℕ) :
      ((W.η (s + 1) * W.δ) u : ℂ) * ((nabs k u ^ ((N : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * N) *
          σ₀ (muAt Ch sel mu cst s P a * cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) a) * N)) := by
    have hC := hA.compl
    have hU := W.unif
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := ComplRes.q_ne_zero hC
    have hvalu := GlobalTheory.TwBridge.PsiRat.val_unif' hU
    have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z)) := by
      obtain ⟨z, hz⟩ := GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hvalu u
      refine ⟨z, ?_⟩
      have hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1 := by
        rw [map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]
        exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)
      exact (ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1
    have hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
      unfold LocE.vP; exact Classical.epsilon_spec hex
    set v := LocE.vP P.1 (qOf P.1) a with hvdef
    set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef
    have hbI : IntAt P.1 b := by
      by_contra h; rw [reduction_eq_zero_of_not_integral P.1 h] at hspec; exact not_isUnit_zero hspec
    have hbv : valuation k (ι b) = 1 := (ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec
    have hb0 : ι b ≠ 0 := by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv
    set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef
    have hu_eq : u = W.ϖ ^ v * ub := by
      ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef,
        mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]
    have hη : W.η (s + 1) ub = 1 := W.unr (s + 1) ub hbv
    have hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := hA.del b ub hbI hspec rfl
    have hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P) := hA.mu s (by rw [hA.steps]; omega)
    have hnU : nabs k ub = 1 := nabs_eq_one_of_valuation_eq_one hbv
    obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU
    have hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹ := by
      rw [nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]
    have hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v) := by
      rw [hu_eq]
      unfold nabs
      rw [map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]
      have h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹ := hnϖ
      have h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1 := hnU
      rw [h1, h2, mul_one, _root_.inv_zpow']
    have hsg : W.sg ≠ 0 := by
      intro h0
      have h2 := congrArg σ₀ (hok.sq_sq P)
      rw [map_pow, hA.sq, h0, zero_mul, map_natCast] at h2
      exact hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)
    have hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹ := by
      unfold muAt LocE.locChar
      rw [ite_eq_right hA.nmem, ← hvdef, ← hbdef]
      congr 1
      unfold LocE.unitV
      rw [dite_eq_left hspec, dite_eq_left hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := by
      rw [hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη,
        Units.val_one, one_mul, hδ]
    have hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ) := by
      have : (qOf P.1 : ℕ) ≠ 0 := fun h => hq0 (by rw [h, Nat.cast_zero])
      exact_mod_cast Nat.pos_of_ne_zero this
    rw [hchar, hn, GlobalTheory.TwBridge.PsiRat.sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]
    push_cast
    have hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1 := by
      rw [neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]
    linear_combination (σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ *
      (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)
  have hsc := char_scalar _ _ hdet (R.N (s + 1) + cOf R (s + 1))
  have hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by
    rw [← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]
    clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'
    unfold Chain.Psi GlobalTheory.SplitWeil.om
    have hn1 : nabs k (1 : kˣ) = 1 := by unfold nabs; rw [map_one, NNReal.coe_one]
    simp only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
    rfl
  have muAt_one : muAt Ch sel mu cst s P 1 = 1 := by
    unfold muAt LocE.locChar
    rw [PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
    have h1 : IsUnit (redP P.1 (1 : X.E)) := by rw [PsiStep.reduction_one']; exact isUnit_one
    unfold LocE.unitV
    rw [dite_eq_left h1]
    have : h1.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])
    rw [this, map_one, Units.val_one]
  rw [hL, hsc]
  unfold PsiAt omPhi Loc.om sgn
  simp only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]
  have h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ
      (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) =
        joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by
    ext v; rfl
  rw [h1]
  simp only [map_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
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

namespace GlobalTheory.Core.Rk.SphCoef

variable {D : D7}

theorem mem_l2_add {A : HSp D} {m : Measure (GA D A)} {φ ψ : GA D A → ℂ} (h : MemL2Quotient (GQ A) m φ)
    (h' : MemL2Quotient (GQ A) m ψ) : MemL2Quotient (GQ A) m (φ + ψ) :=
  ⟨fun γ hγ g => by simp only [Pi.add_apply, h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩

theorem mem_l2_smul {A : HSp D} {m : Measure (GA D A)} {φ : GA D A → ℂ} (c : ℂ) (h : MemL2Quotient (GQ A) m φ) :
    MemL2Quotient (GQ A) m (c • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul c⟩

theorem mem_l2_zero {A : HSp D} {m : Measure (GA D A)} : MemL2Quotient (GQ A) m (0 : GA D A → ℂ) :=
  ⟨fun _ _ _ => rfl, MemLp.zero⟩

theorem isSphCoef_rcoef : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  intro hP D θ A cA L hθ m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hv x hx
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  have h1 : MemL2Quotient (GQ A) m u₁ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₁).1
  have h2 : MemL2Quotient (GQ A) m u₂ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₂).1
  have hR : ∀ g, MemL2Quotient (GQ A) m (rTr A g u₁) := fun g => h1.mul_right g
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m (rTr A x F)}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ℓ₀ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left F.2 G.2 h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  let ρ : Representation ℂ (Gv A v) (GA D A → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp (emb D.sp.cm.sig A.gram v)
  have hρ : ∀ y g, ρ y u₁ g = u₁ (g * emb D.sp.cm.sig A.gram v y) := fun _ _ => rfl
  have htr : ∀ y, rTr A x (ρ y u₁) = rTr A (x * emb D.sp.cm.sig A.gram v y) u₁ := fun y => funext fun g => by
    simp only [rTr, hρ, mul_assoc]
  have hmem : ∀ y, ρ y u₁ ∈ p := fun y => by
    show MemL2Quotient _ _ (rTr A x (ρ y u₁))
    rw [htr]; exact hR _
  have hval : ∀ y, ℓ (ρ y u₁) = petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂ := fun y => by
    have e := LinearMap.congr_fun hℓ ⟨_, hmem y⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
    rw [e, ← htr]; rfl
  have hnorm : ∀ g, ‖(hR g).toL2‖ = ‖h1.toL2‖ := fun g => by
    have e1 := (hR g).inner_toL2_eq_theta_pairing (hR g)
    have e2 := h1.inner_toL2_eq_theta_pairing h1
    have e3 : pet (GQ A) m (rTr A g u₁) (rTr A g u₁) = pet (GQ A) m u₁ u₁ := by
      have := petersson_rTr (μ := m) h1 h1 g
      exact this
    rw [e3, ← e2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
    have e4 : ‖(hR g).toL2‖ ^ 2 = ‖h1.toL2‖ ^ 2 := by exact_mod_cast e1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e4
  refine ⟨⟨‖h2.toL2‖ * ‖h1.toL2‖, fun y => ?_⟩, GA D A → ℂ, inferInstance, inferInstance, ρ, u₁, ℓ,
    fun w h => hpar v (by simpa using hv) w h, fun k hk y => ?_, fun y => (hval y).symm⟩
  · show ‖petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂‖ ≤ _
    rw [petersson, ← (hR _).inner_toL2_eq_theta_pairing h2, ← hnorm (x * emb D.sp.cm.sig A.gram v y)]
    exact norm_inner_le_norm _ _
  · rw [hval, hval, map_mul]
    have hc : emb D.sp.cm.sig A.gram v k * x = x * emb D.sp.cm.sig A.gram v k :=
      (GlobalTheory.AdelicU.commute_emb (σ := D.sp.cm.sig) (J := A.gram) k hx).eq
    have e1 : rTr A (x * (emb D.sp.cm.sig A.gram v k * emb D.sp.cm.sig A.gram v y)) u₁ =
        rTr A (emb D.sp.cm.sig A.gram v k) (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) := funext fun g => by
      simp only [rTr]
      rw [← mul_assoc x, ← hc]
      simp only [mul_assoc]
    have e2 : u₂ = rTr A (emb D.sp.cm.sig A.gram v k) u₂ := funext fun g => (hsph v hv k hk g).symm
    rw [e1]
    conv_lhs => rw [e2]
    exact petersson_rTr (hR _) h2 _

end GlobalTheory.Core.Rk.SphCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincPet

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem value_laws (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (hχ : ∀ k ∈ J, χ k = 1)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    ∀ v, Continuous (U v) ∧ (∃ C : ℝ, ∀ g, ‖U v g‖ ≤ C) ∧ ∀ k ∈ J, ∀ g, U v (g * k) = U v g := by
  unfold Mult at hU
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v
    refine ⟨(hT.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut v) (hT.cusp v), fun k hk g => ?_⟩
    rw [hT.lev v k hk g, hχ k hk, one_mul]
  | zero =>
    intro v
    exact ⟨continuous_const, ⟨0, fun g => by simp⟩, fun k _ g => by simp⟩
  | add U U' _ _ h h' =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    obtain ⟨c2, ⟨C2, b2⟩, i2⟩ := h' v
    refine ⟨by simpa using c1.add c2, ⟨C1 + C2, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))
    · simp only [MultilinearMap.add_apply, Pi.add_apply, i1 k hk g, i2 k hk g]
  | smul a U _ h =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    refine ⟨by simpa using c1.const_smul a, ⟨‖a‖ * C1, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, i1 k hk g]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_triv (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  have hP : (R.datWp i R.triv).P = LevelP.triv R.Pg D.R.r ℂ := rfl
  have hs : (R.datWp i R.triv).s = 0 := rfl
  have hQ : (R.datWp i R.triv).Q = ∅ := rfl
  have hchi : ∀ (Q : LevelP R.Pg D.R.r ℂ), Q = LevelP.triv R.Pg D.R.r ℂ → ∀ y : Q.H, Q.chi y = 1 := by
    rintro _ rfl y; rfl
  have h1 : ∀ x, ext1 (R.datWp i R.triv).P.H (⇑(R.datWp i R.triv).P.chi) x = 1 := by
    intro x
    unfold ext1
    split
    · exact hchi _ hP _
    · rfl
  simp only [levChi, levFn, h1, hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one,
    Units.val_one]

end GlobalTheory.PrincPet

namespace GlobalTheory.PrincPet

theorem petW_continuous_rightInv : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i σ, IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)} ∧ ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec, (Continuous fun g => petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂)) ∧ ∀ g, ∀ k ∈ levW R i, petW R i (rTr (Wc D i) (g * k) (U₁ v₁)) (U₂ v₂) = petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hC i σ
  refine ⟨GlobalTheory.AdelicScalar.isOpen_level (Wc D i) (R.βW i) (R.datWp i R.triv), ?_⟩
  intro U₁ hU₁ U₂ hU₂ v₁ v₂
  have hθ : IsInfFam R.θ := hC.models.inf
  have hχ : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := fun k _ => levChi_triv R i k
  obtain ⟨c₁, ⟨C₁, b₁⟩, inv₁⟩ := value_laws hP hθ hχ hU₁ v₁
  obtain ⟨c₂, ⟨C₂, b₂⟩, -⟩ := value_laws hP hθ hχ hU₂ v₂
  refine ⟨?_, fun g k hk => ?_⟩
  · have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hμ := (hC.models.νW i).1.1
    have hfin : R.νW i (R.fdW i) < ⊤ :=
      GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Wc D i) (R.νW i) (R.fdW i) hμ (hC.models.νW i).2
    haveI : IsFiniteMeasure ((R.νW i).restrict (R.fdW i)) := isFiniteMeasure_restrict.2 hfin.ne
    have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (b₁ 1)
    show Continuous fun g => ∫ x in R.fdW i, rTr (Wc D i) g (U₁ v₁) x * starRingEnd ℂ (U₂ v₂ x) ∂(R.νW i)
    refine continuous_of_dominated (bound := fun _ => C₁ * C₂) (fun g => ?_) (fun g => ?_) (integrable_const _) ?_
    · exact ((c₁.comp (continuous_id.mul continuous_const)).mul
        (Complex.continuous_conj.comp c₂)).aestronglyMeasurable
    · refine .of_forall fun x => ?_
      simp only [rTr, norm_mul, Complex.norm_conj]
      exact mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) hC₁
    · exact .of_forall fun x => (c₁.comp (continuous_const.mul continuous_id)).mul continuous_const
  · have e : rTr (Wc D i) (g * k) (U₁ v₁) = rTr (Wc D i) g (U₁ v₁) := by
      funext x
      simp only [rTr]
      rw [← mul_assoc]
      exact inv₁ k hk (x * g)
    rw [e]

end GlobalTheory.PrincPet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPoint
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Eis

theorem modGrowth_eis_sph : GlobalTheory.Published.SiegelEisensteinContinuation → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  intro hP D V h0 a ha hI σ hσ
  have hμ : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hb : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  have hφ := sph_mem hI (σ : ℂ)
  obtain ⟨k, hk⟩ := (hP D V h0 a ha hI 1 0 hμ hb σ _ hφ).2 σ
  have hv := (sphConv D V a hI).eisValueAt_flat hI hφ hμ (by simpa using hσ)
  obtain ⟨r, hr, -, -, C, N, h⟩ := hk.of_eisValueAt hv
  exact ⟨C, N, fun g => hv.eisCont_eq ▸ h σ (Metric.mem_ball_self hr) g⟩

end GlobalTheory.Eis

end
end

