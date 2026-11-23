module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.DetNeZeroOfNearOne
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.RkX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_ne_zero_of_near_one {j : ℕ} (A : Matrix (Fin j) (Fin j) k)
    (hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1) : A.det ≠ 0 := by
  have hint : ∀ i l, A i l ∈ 𝒪[k] := by
    intro i l
    have h1 : valuation k ((1 : Matrix (Fin j) (Fin j) k) i l) ≤ 1 := by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    have : A i l = (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) + (1 : Matrix (Fin j) (Fin j) k) i l := by ring
    show valuation k (A i l) ≤ 1
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hA i l).le h1)
  let y : Matrix (Fin j) (Fin j) 𝒪[k] := Matrix.of fun i l => ⟨A i l, hint i l⟩
  have hy : (algebraMap 𝒪[k] k).mapMatrix y = A := by
    ext i l; rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix y = 1 := by
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (1 : Matrix (Fin j) (Fin j) (IsLocalRing.ResidueField 𝒪[k])) i l
        = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    have e : algebraMap 𝒪[k] k (y i l - (1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l)
        = A i l - (1 : Matrix (Fin j) (Fin j) k) i l := by
      by_cases h : i = l
      · subst h; simp [y]; rfl
      · simp [y, Matrix.one_apply_ne h]; rfl
    rw [e]
    exact (hA i l).ne
  have hdet : IsLocalRing.residue 𝒪[k] y.det = 1 := by
    rw [RingHom.map_det, hres, Matrix.det_one]
  intro h0
  have : y.det = 0 := by
    apply Subtype.ext
    have := congrArg (fun M => M.det) hy
    rw [← RingHom.map_det] at this
    rw [← this] at h0
    exact h0
  rw [this, map_zero] at hdet
  exact zero_ne_one hdet

end PositivityTheory.Tls2.Ming3.RkX

namespace PositivityTheory.Tls2.Ming3

theorem rk : RkSt := by
  intro k _ _ _ _ n r j hjn hjr c hc x hx
  let A : Matrix (Fin j) (Fin j) k := x.submatrix (Fin.castLE hjn) (Fin.castLE hjr)
  have hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1 := by
    intro i l
    have h := hx (Fin.castLE hjn i) (Fin.castLE hjr l)
    have e : idem k r n j (Fin.castLE hjn i) (Fin.castLE hjr l) = (1 : Matrix (Fin j) (Fin j) k) i l := by
      show (if (i : ℕ) = l ∧ (l : ℕ) < j then (1 : k) else 0) = _
      by_cases h : i = l
      · subst h; simp
      · have h' : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
        simp [Matrix.one_apply_ne h, h']
    rw [e] at h
    exact h.trans_lt hc
  have hdet := RkX.det_ne_zero_of_near_one A hA
  have h1 : A.rank = j := by
    rw [Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc j = A.rank := h1.symm
    _ ≤ x.rank := Matrix.rank_submatrix_le x _ _

end PositivityTheory.Tls2.Ming3
end

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.Imports
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3

theorem cov : CovSt := by
  intro k _ _ _ _ _ _ ν hν n r h g Φ
  haveI : ν.IsAddHaarMeasure := hν.1
  rw [GlobalTheory.SplitWeil.integral_comp_mul_mul_volM ν g h Φ]
  simp only [Fintype.card_fin, Complex.real_smul]

end PositivityTheory.Tls2.Ming3
end

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.LFrob
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.Tls2.Ming3.FrobX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin (r + t)) k) W}

abbrev lrep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem lrep_tmul (g : Levi k (Two (Fin r) (Fin t))) (v : V) :
    lrep t μ σ g (v ⊗ₜ[ℂ] (1 : ℂ)) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        (σ (g false : GL (Fin r) k) v ⊗ₜ[ℂ] (1 : ℂ)) := by
  change σ (g false) v ⊗ₜ[ℂ] ((μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) • (1 : ℂ)) = _
  rw [TensorProduct.tmul_smul]

def fn (π : Representation ℂ (GL (Fin (r + t)) k) W) (ev : W →ₗ[ℂ] V) (w : W) :
    GL (Fin (r + t)) k → V ⊗[ℂ] ℂ :=
  fun h => ev (π h w) ⊗ₜ[ℂ] (1 : ℂ)

theorem fn_law {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k) :
    fn π ev w (p * g) =
      ((twist (lrep t μ σ) (deltaHalf k (Two (Fin r) (Fin t)))).comp
        (leviProj k (two (stdSum (rfl : r + t = r + t))))) p (fn π ev w g) := by
  rw [MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply]
  simp only [PositivityTheory.Tls2.Ming3.FrobX.fn]
  rw [PositivityTheory.Tls2.Ming3.FrobX.lrep_tmul, smul_smul, TensorProduct.smul_tmul', map_mul,
    Module.End.mul_apply, hl p (π g w)]

def elt (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (lrep t μ σ) :=
  ⟨⟨fn π ev w, fun p g => fn_law hl w p g⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) (by
      intro g hg
      have hg' : π g w = w := hg
      refine Subtype.ext (funext fun x => ?_)
      show fn π ev w (x * g) = fn π ev w x
      simp only [fn, map_mul, Module.End.mul_apply, hg']))⟩

def frobMap (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) :
    π.IntertwiningMap (prod₂ σ (detRep (Fin t) μ)) where
  toFun w := elt hπ hl w
  map_add' w w' := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (w + w')) ⊗ₜ[ℂ] (1 : ℂ) = ev (π h w) ⊗ₜ[ℂ] (1 : ℂ) + ev (π h w') ⊗ₜ[ℂ] (1 : ℂ)
    simp [TensorProduct.add_tmul]))
  map_smul' c w := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (c • w)) ⊗ₜ[ℂ] (1 : ℂ) = c • (ev (π h w) ⊗ₜ[ℂ] (1 : ℂ))
    simp [TensorProduct.smul_tmul']))
  isIntertwining' g := by
    refine LinearMap.ext fun w => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ev (π x (π g w)) ⊗ₜ[ℂ] (1 : ℂ) = ev (π (x * g) w) ⊗ₜ[ℂ] (1 : ℂ)
    rw [map_mul, Module.End.mul_apply]

end PositivityTheory.Tls2.Ming3.FrobX

namespace PositivityTheory.Tls2.Ming3

theorem frob : FrobSt := by
  intro k _ _ _ _ r t μ V _ _ W _ _ σ π ev hπ hev hl
  refine ⟨PositivityTheory.Tls2.Ming3.FrobX.frobMap hπ hl, fun h => hev ?_⟩
  refine LinearMap.ext fun w => ?_
  have h1 : ev (π 1 w) ⊗ₜ[ℂ] (1 : ℂ) = 0 :=
    congrArg (fun x => x.1.1 (1 : GL (Fin (r + t)) k)) (LinearMap.congr_fun h w)
  rw [map_one, Module.End.one_apply] at h1
  have h2 := congrArg (TensorProduct.rid ℂ V) h1
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h2
  rw [LinearMap.zero_apply]
  exact h2

end PositivityTheory.Tls2.Ming3
end
end

