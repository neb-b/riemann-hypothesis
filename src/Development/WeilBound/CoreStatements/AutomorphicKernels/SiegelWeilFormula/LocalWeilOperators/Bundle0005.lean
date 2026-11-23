module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.T_lin (d : SD σ) (a : ℂ) (Φ Φ' : d.Fn) : d.T (a • Φ + Φ') = a • d.T Φ + d.T Φ' := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (a • Φ + Φ') = a • schr d.B.ψ p Φ + schr d.B.ψ p Φ' :=
    fun p => by
      funext x
      simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simp only [SD.T, Darboux.rho, h, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]

theorem isSw_lin {m n : ℕ} {f g : (Fin m → Fin n → ℂ) → ℂ} (a : ℂ) (hf : IsSw f) (hg : IsSw g) : IsSw (a • f + g) := by
  obtain ⟨φ, hφ⟩ := hf
  obtain ⟨φ', hφ'⟩ := hg
  exact ⟨a • φ + φ', by funext u; simp [← hφ, ← hφ']⟩

theorem tens_cancel {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (h0 : Ψ ≠ 0) {g g' : d.LF}
    (h : R.tens w g Ψ = R.tens w g' Ψ) : g = g' := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  funext u
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
  have := congrFun h (X₀ + Z)
  simp only [RD.tens, hZ3, hΨ X₀ Z hZ1 hZ2] at this
  exact mul_right_cancel₀ hX₀ this

theorem exists_adm (hT : TAll) {Ψ : d.MF} (hΨ : R.GoodAway w Ψ) {f : d.LF} (hf : IsSw f) :
    ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ := (hT.1 F E σ d).2.1 _ (hΨ.2.2 f hf)

theorem locOp_one (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) : ∀ f, IsSw f → L 1 f = f := by
  intro f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e := (hL 1 f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_one, map_one, Module.End.one_apply, hT'] at e
  exact (R.tens_cancel hΨ.1 hΨ.2.1 e).symm

theorem locOp_mul (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ y y' f, IsSw f → L (y * y') f = L y (L y' f) := by
  intro y y' f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y' f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := (hL y (L y' f) (hL y' f hf).1).2 Ψ hΨ.1 _ (d.om_sch _ Φ hΦ) e1
  have e3 := (hL (y * y') f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_mul, map_mul, Module.End.mul_apply] at e3
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e3.symm.trans e2)

theorem locOp_lin (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ y (a : ℂ) f g, IsSw f → IsSw g → L y (a • f + g) = a • L y f + L y g := by
  intro y a f g hf hg
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φf, hΦf, hTf⟩ := R.exists_adm hT hΨ hf
  obtain ⟨Φg, hΦg, hTg⟩ := R.exists_adm hT hΨ hg
  have hΦ : a • Φf + Φg ∈ d.sch := d.sch.add_mem (d.sch.smul_mem a hΦf) hΦg
  have hTΦ : d.T (a • Φf + Φg) = R.tens w (a • f + g) Ψ := by
    rw [d.T_lin, hTf, hTg]
    funext X
    simp only [RD.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e := (hL y (a • f + g) (isSw_lin a hf hg)).2 Ψ hΨ.1 _ hΦ hTΦ
  have ef := (hL y f hf).2 Ψ hΨ.1 Φf hΦf hTf
  have eg := (hL y g hg).2 Ψ hΨ.1 Φg hΦg hTg
  rw [map_add (f := _), map_smul, d.T_lin, ef, eg] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp only [RD.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem locOp_nU (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSw f →
      L y f = fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u := by
  intro y b hb hy f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepN w hT y b hb hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)

theorem locOp_mM (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ c : Matrix (Fin d.n) (Fin d.n) ℂ → ℂ, (∀ a, IsUnit a.det → c a ≠ 0) ∧
      ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
        L y f = fun u => c a * f (Matrix.of u * a) := by
  classical
  have hinj : ∀ y y' : GR d.n, mR y = mR y' → y = y' := fun y y' h => Subtype.ext (Units.ext h)
  refine ⟨fun a => if h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a then
    (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose else 1, fun a ha => ?_, fun y a ha hy f hf => ?_⟩
  · by_cases h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a
    · dsimp only
      rw [dif_pos h]
      exact (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.1
    · dsimp only
      rw [dite_eq_right h]
      exact one_ne_zero
  · have h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a := ⟨ha, y, hy⟩
    have hy0 : h.2.choose = y := hinj _ _ (h.2.choose_spec.trans hy.symm)
    simp only [dif_pos h]
    have hs := (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.2
    rw [← hy0]
    obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e1 := (hL h.2.choose f hf).2 Ψ hΨ.1 Φ hΦ hT'
    have e2 := (hs.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)

end RD

end PositivityTheory.SiegelWeilFormula

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMVal
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem compFin_det (t : GL (Fin d.n) (AE F E)) (hf : finOne F • t.1 = finOne F • 1) (v : Pl (F := F)) :
    compFin F E v (t.1.det) = 1 := by
  have hm : t.1.map (compFin F E v) = 1 := by
    ext i j
    rw [Matrix.map_apply, ← Place.compFin_finOne v (t.1 i j)]
    change compFin F E v ((finOne F • t.1) i j) = _
    rw [hf, Matrix.smul_apply, Place.compFin_finOne, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]

theorem piInf_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (w' : InfinitePlace F) :
    piInf (d.B.emb w') (t.1.det) = Function.update (fun _ => (1 : ℂ)) w a.det w' := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  by_cases h : w' = w
  · subst h
    rw [Function.update_self]
    exact congrArg Matrix.det ht
  · rw [Function.update_of_ne h]
    have := congrArg Matrix.det (ho w' h)
    rw [Matrix.det_one] at this
    exact this

theorem det_uW (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    t.1.det = d.uW w a.det := by
  obtain ⟨-, hs2, hs3, -, -⟩ := (Place.exists_sec d.cm d.B.emb).choose_spec
  apply PositivityTheory.ThKG.Tow.Levi.ad_ext d.cm d.B.emb
  · intro w'
    rw [piInf_det (d := d) w t a ht ho w', SD.uW, map_add (f := _), hs2, Place.piInf_finOne, add_zero]
  · intro v
    rw [compFin_det (d := d) t hf v, SD.uW, map_add (f := _), ← Place.compFin_finOne v, hs3, map_zero, zero_add,
      Place.compFin_finOne, map_one]

theorem chi_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = d.chiW w a.det := by
  have e := det_uW (d := d) w t a ht ho hf
  have hu : IsUnit (d.uW w a.det) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.det t).isUnit.map (RingHom.id _) |>.map (RingHom.id _) |> fun h => by
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  rw [SD.chiW, dite_eq_left hu]
  have : hu.unit = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by rw [IsUnit.unit_spec, Matrix.GeneralLinearGroup.val_det_apply, e])
  rw [this]

theorem absE_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖a.det‖ ^ 2 := by
  rw [GlobalTheory.Doubling.absE_apply]
  have hinf : ∀ w', GlobalTheory.Doubling.absEw F E w' (GlobalTheory.Doubling.unitInf F E w' (Matrix.GeneralLinearGroup.det t)) =
      ‖Function.update (fun _ => (1 : ℂ)) w a.det w'‖₊ ^ 2 := by
    intro w'
    rw [GlobalTheory.Doubling.absEw_eq_sq d.cm (d.B.emb w'), ← piInf_det (d := d) w t a ht ho w',
      ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) = 1 := by
    intro v
    have : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = 1 := by
      apply Units.ext
      show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = 1
      rw [Matrix.GeneralLinearGroup.val_det_apply, compFin_det (d := d) t hf v]
    rw [this, map_one]
  simp only [hinf, hfin, finprod_one, mul_one]
  rw [Finset.prod_eq_single w (fun w' _ h => by rw [Function.update_of_ne h]; simp) (fun h => absurd (Finset.mem_univ w) h),
    Function.update_self]
  push_cast
  rfl

theorem stepM_val_pf (hT : TAll) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  obtain ⟨t, ht, ho, hf, hS⟩ := R.stepM_gen w hT y a ha hy
  have hc : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) =
      d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m := by
    rw [chi_det (d := d) w t a ht ho hf, absE_det (d := d) w t a ht ho hf, ← Real.rpow_natCast ‖a.det‖ 2,
      ← Real.rpow_mul (norm_nonneg _), show ((2 : ℕ) : ℝ) * ((d.m : ℝ) / 2) = (d.m : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rfl
  simp only [hc] at hS
  exact hS

end RD

end PositivityTheory.SiegelWeilFormula

end
end

