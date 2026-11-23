module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.TwBridge.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymBridge GlobalTheory.SymTieExists

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

section Add
variable {E K k : Type} [Field E] [NumberField E] [Field K]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Add

section Tw
variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem sg_sq (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) : W.sg ^ 2 = 1 := by
  have h1 := congrArg σ₀ (hok.sq_sq P)
  have hq := ComplRes.q_ne_zero h.compl
  have hq' : (qOf P.1 : ℂ) ≠ 0 := fun h0 => hq (by rw [show qOf P.1 = 0 by exact_mod_cast h0]; simp)
  rw [map_pow, h.sq, mul_pow, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h1
  exact mul_right_cancel₀ hq' (by simpa using h1)

theorem isGL_existsUnique (j c : ℕ) (hc : cOf R j = c) (γ : AutY X R j) :
    ∃! g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k, IsGL ι γ g := by
  subst hc
  obtain ⟨d, hd⟩ := GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t j
  obtain ⟨e, he⟩ := GlobalTheory.AtTypeExists.exists_ord.2.2.1 _ (R.N j) (cOf R j) _ d hd
  have key : ∀ a b : AutY X R j, toLoc ι e e a.toLinearMap * toLoc ι e e b.toLinearMap = toLoc ι e e (a * b).toLinearMap := by
    intro a b
    ext i l
    have : b (Pi.single (e l) 1) = ∑ m, b (Pi.single (e l) 1) (e m) • (Pi.single (e m) 1 : Fin _ → X.E) := by
      rw [Equiv.sum_comp e (fun m => b (Pi.single (e l) 1) m • (Pi.single m 1 : Fin _ → X.E))]
      ext z; simp [Finset.sum_apply, Pi.single_apply]
    change ∑ m, ι (a (Pi.single (e m) 1) (e i)) * ι (b (Pi.single (e l) 1) (e m)) = ι (a (b (Pi.single (e l) 1)) (e i))
    conv_rhs => rw [this]
    simp [Finset.sum_apply, mul_comm]
  have one : toLoc ι e e (1 : AutY X R j).toLinearMap = 1 := by
    ext i l
    change ι ((Pi.single (e l) 1 : Fin _ → X.E) (e i)) = _
    simp [Pi.single_apply, Matrix.one_apply, apply_ite ι]
  refine ⟨⟨toLoc ι e e γ.toLinearMap, toLoc ι e e (γ⁻¹).toLinearMap, by rw [key, mul_inv_cancel, one],
    by rw [key, inv_mul_cancel, one]⟩, ⟨e, he, rfl⟩, ?_⟩
  rintro g ⟨e', he', hg⟩
  obtain rfl : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
  exact Units.ext hg

end Tw

section Sign
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem valuation_spec (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) {a : X.E} (ha : a ≠ 0) :
    IntAt P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a) ∧
      IsUnit (redP P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P.1 (ComplRes.q_not_mem_sq h.compl W.unif)
  have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / (qOf P.1 : X.E) ^ z)) := by
    have h0 : P.1.valuation X.E a ≠ 0 := by simpa using ha
    refine ⟨-WithZero.log (P.1.valuation X.E a), ?_⟩
    set b := a / (qOf P.1 : X.E) ^ (-WithZero.log (P.1.valuation X.E a)) with hb
    have h1 : P.1.valuation X.E b = 1 := by
      rw [hb, map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log h0, h0]
    have i1 := (GlobalTheory.AtTypeExists.intAt_iff P.1 b).2 h1.le
    have i2 := (GlobalTheory.AtTypeExists.intAt_iff P.1 b⁻¹).2 (by rw [map_inv₀, h1, inv_one])
    have b0 : b ≠ 0 := fun h0 => by simp [h0] at h1
    refine (ComplRes.v_eq_one_iff_red h.compl W.unif i1).1 (le_antisymm (ComplRes.v_le_one h.compl i1) ?_)
    have := ComplRes.v_le_one h.compl i2
    rw [map_inv₀, map_inv₀] at this
    exact (inv_le_one₀ (by simpa [zero_lt_iff] using b0)).1 this
  have hu := Classical.epsilon_spec hex
  refine ⟨?_, hu⟩
  by_contra hn
  have : redP P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a) = 0 :=
    dif_neg fun ⟨_, r, t, ht, e, _⟩ => hn ⟨r, t, ht, e⟩
  exact hu.ne_zero this

theorem mu_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (i : ℕ) (hi : i < R.m) {a : X.E} (u : kˣ) (hu : (u : k) = ι a) :
    ((W.T s R).mu (i + 1) u : ℂ) = σ₀ (muAt Ch sel mu cst i P a) := by
  have ha : a ≠ 0 := fun h0 => u.ne_zero (by rw [hu, h0, map_zero])
  obtain ⟨h1, h2⟩ := valuation_spec sel mu cst σ₀ P ι s W h ha
  set z := LocE.vP P.1 (qOf P.1) a with hz
  have e : ((u * W.ϖ ^ (-z) : kˣ) : k) = ι (a / (qOf P.1 : X.E) ^ z) := by
    rw [map_div₀, map_zpow₀, ← h.compl.unif, ← hu]; simp [div_eq_mul_inv]
  have h3 := h.del _ _ h1 h2 e
  have h4 := W.unr (i + 1) _ (by rw [e]; exact (ComplRes.v_eq_one_iff_red h.compl W.unif h1).2 h2)
  have h5 : u = W.ϖ ^ z * (u * W.ϖ ^ (-z)) := by simp [mul_comm u]
  change ((W.η (i + 1) * W.δ) u : ℂ) = _
  rw [h5, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, h.mu i hi, MonoidHom.mul_apply, h4, one_mul, h3,
    muAt, LocE.locChar, if_neg h.nmem, ← hz, map_mul, map_zpow₀, LocE.unitV, LocE.unitV, dite_eq_left h2, dite_eq_left h2]
  simp

theorem nabs_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) {a : X.E} (u : kˣ) (hu : (u : k) = ι a) (n : ℕ) :
    ((nabs k u ^ ((n : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * n) * σ₀ (cst.sq P ^ (-LocE.vP P.1 (qOf P.1) a * n)) ∧
      ((nabs k u ^ (-(n : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * n) * σ₀ (cst.sq P ^ (LocE.vP P.1 (qOf P.1) a * n)) := by
  have ha : a ≠ 0 := fun h0 => u.ne_zero (by rw [hu, h0, map_zero])
  obtain ⟨h1, h2⟩ := valuation_spec sel mu cst σ₀ P ι s W h ha
  set z := LocE.vP P.1 (qOf P.1) a with hz
  have e : ((u * W.ϖ ^ (-z) : kˣ) : k) = ι (a / (qOf P.1 : X.E) ^ z) := by
    rw [map_div₀, map_zpow₀, ← h.compl.unif, ← hu]; simp [div_eq_mul_inv]
  have h4 := nabs_eq_one_of_valuation_eq_one (x := u * W.ϖ ^ (-z))
    (by rw [e]; exact (ComplRes.v_eq_one_iff_red h.compl W.unif h1).2 h2)
  have hlt := ComplRes.v_unif_lt_one W.unif
  have hirr : Irreducible (⟨W.ϖ, (Valuation.mem_integer_iff _ _).2 hlt.le⟩ : 𝒪[k]) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, W.unif,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le]
    rfl
  have h6 := nabs_uniformiser hirr (x := W.ϖ) rfl
  rw [ComplRes.resCard_eq h.compl W.unif] at h6
  have hq := ComplRes.q_ne_zero h.compl
  have hq0 : (0 : ℝ) < qOf P.1 := by
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => hq (by rw [h0]; simp)
  have h7 : nabs k u = (qOf P.1 : ℝ) ^ (-z) := by
    have : nabs k (u * W.ϖ ^ (-z)) = nabs k u * nabs k W.ϖ ^ (-z) := by simp [nabs]
    rw [h4, h6, _root_.inv_zpow', neg_neg] at this
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_left this.symm
  have hs := sg_sq sel mu cst σ₀ P ι s W h hok
  have hs0 : W.sg ≠ 0 := fun h0 => by simp [h0] at hs
  have key : ∀ t : ℤ, (((qOf P.1 : ℝ) ^ ((t : ℝ) / 2) : ℝ) : ℂ) = W.sg ^ t * σ₀ (cst.sq P ^ t) := fun t => by
    rw [map_zpow₀, h.sq, mul_zpow, ← mul_assoc, ← mul_zpow, ← pow_two, hs, _root_.one_zpow, one_mul, ← Complex.ofReal_zpow,
      Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; ring
  have hneg : ∀ t : ℤ, W.sg ^ (-t) = W.sg ^ t := fun t => by
    rw [_root_.zpow_neg]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_zpow, ← pow_two, hs, _root_.one_zpow]
  constructor
  · rw [← hneg, ← neg_mul, ← key, h7, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; push_cast; ring
  · rw [← key, h7, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; push_cast; ring

theorem toLoc_eq {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → X.E) →ₗ[X.E] (Fin a → X.E)) :
    toLoc ι e e' x = ((LinearMap.toMatrix' x).map ι).submatrix e e' := by
  ext i l; simp [toLoc, LinearMap.toMatrix'_apply]

theorem toLoc_mul {A B C : Type} [Fintype B] {a b c : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (e'' : C ≃ Fin c)
    (x : (Fin b → X.E) →ₗ[X.E] (Fin a → X.E)) (y : (Fin c → X.E) →ₗ[X.E] (Fin b → X.E)) :
    toLoc ι e e' x * toLoc ι e' e'' y = toLoc ι e e'' (x ∘ₗ y) := by
  rw [toLoc_eq, toLoc_eq, toLoc_eq, submatrix_mul_equiv, LinearMap.toMatrix'_comp, Matrix.map_mul]

theorem det_toLoc {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) (γ : (Fin a → X.E) ≃ₗ[X.E] (Fin a → X.E))
    (g : GL A k) (hg : g.val = toLoc ι e e γ.toLinearMap) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι (LinearEquiv.det γ : X.Eˣ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, toLoc_eq, det_submatrix_equiv_self, LinearEquiv.coe_det,
    ← LinearMap.det_toMatrix', RingHom.map_det]
  rfl

theorem om_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) (j c c' : ℕ) (hj : j < R.m)
    (e' : XIx (Fin R.k) (Fin R.t) j ⊕ Fin c' ≃ Fin (R.N j + cOf R j))
    (e : XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin c ≃ Fin (R.N (j + 1) + cOf R (j + 1)))
    (a : AutY X R j) (b : AutY X R (j + 1)) (g : GL _ k) (g' : GL _ k) (hg : g.val = toLoc ι e' e' a.toLinearMap)
    (hg' : g'.val = toLoc ι e e b.toLinearMap) (Φ : Matrix _ _ k → ℂ) (ΦE : Loc.SF X.E X.K _ _)
    (hΦ : ∀ x, Φ (toLoc ι e e' x) = σ₀ (ΦE x)) (x) :
    om ((W.T s R).mu (j + 1)) g g' Φ (toLoc ι e e' x) =
      sgn sel mu P W a (R.N (j + 1) + cOf R (j + 1)) * sgn sel mu P W b (R.N j + cOf R j) *
        σ₀ (Loc.om (muAt Ch sel mu cst j P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) a b ΦE x) := by
  have d := det_toLoc ι e' a g hg
  have d' := det_toLoc ι e b g' hg'
  have hi : (g'⁻¹).val = toLoc ι e e b.symm.toLinearMap := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg', toLoc_mul, LinearEquiv.comp_symm, toLoc_eq]
    simp
  unfold om Loc.om sgn
  rw [hi, hg, toLoc_mul, toLoc_mul, hΦ, Units.val_inv_eq_inv_val, mu_agree Ch sel mu cst σ₀ P ι s W h j hj _ d,
    mu_agree Ch sel mu cst σ₀ P ι s W h j hj _ d', Fintype.card_congr e, Fintype.card_congr e', Fintype.card_fin, Fintype.card_fin,
    (nabs_agree sel mu cst σ₀ P ι s W h hok _ d _).1, (nabs_agree sel mu cst σ₀ P ι s W h hok _ d' _).2]
  simp only [map_mul, map_inv₀, LinearMap.comp_assoc]
  ring

end Sign

end GlobalTheory.TwBridge.Model
