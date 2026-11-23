module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

abbrev thC (n : ℕ) : Monoid.End (GL (Fin n) ℂ) := thetaR (starRingEnd ℂ) n

theorem nil_sq_mul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) : X * X * X = 0 := by
  have h : ∀ y, (X * X * X) *ᵥ y = 0 := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hX.1 y))
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

def uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) : GL (Fin n) ℂ where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp
  inv_val := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp

@[simp] theorem uOf_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) :
    (uOf X).val = 1 + X.1 := rfl

theorem continuous_uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    Continuous (uOf : nilrad W₁ W₂ → GL (Fin n) ℂ) := by
  have h : Continuous fun X : nilrad W₁ W₂ => X.1 := continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add h
  · have : Continuous fun X : nilrad W₁ W₂ => (1 - X.1 + X.1 * X.1 : Matrix (Fin n) (Fin n) ℂ) :=
      (continuous_const.sub h).add (h.matrix_mul h)
    exact this

def NilChange : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ Φ : nilrad W₁ W₂ → nilrad W₁ W₂, Continuous Φ ∧
    (∀ X, uOf (Φ X) = (uOf X)⁻¹ * (d * thC n (uOf X) * d⁻¹)) ∧
    ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure], ∃ c : NNReal, ν.map Φ = (c : ENNReal) • ν

def QuotVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∀ F : GL (Fin n) ℂ → ℂ, Measurable F → (∀ t ∈ twCent (thC n) d, ∀ x, F (t * x) = F x) →
    (∀ x k, thC n k = k → F (x * k) = F x) →
    (∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure] (q : GL (Fin n) ℂ), ∫ X, F (uOf X * q) ∂ν = 0) →
    quotIntegral μ (twCent (thC n) d) μd F = 0

theorem mem_img' (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  have e1 : ∀ z : Fin n → ℂ, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ (g.val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e2 : ∀ z : Fin n → ℂ, g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, e1]; exact hx
  · intro h
    exact ⟨_, h, by rw [Matrix.toLin'_apply, e2]⟩

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img (a * b) W = img a (img b W) := by
  ext y
  simp only [mem_img', _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  ext y
  simp [mem_img']

theorem thC_val (q : GL (Fin n) ℂ) : (thC n q).val = (q⁻¹ : GL (Fin n) ℂ).valᴴ := by
  rw [thC, thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]

theorem mem_perp' (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perp (starRingEnd ℂ) W ↔ ∀ x ∈ W, star x ⬝ᵥ y = 0 := Iff.rfl

theorem perp_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perp (starRingEnd ℂ) (img q W) = img (thC n q) (perp (starRingEnd ℂ) W) := by
  have hi : ((thC n q)⁻¹ : GL (Fin n) ℂ).val = q.valᴴ := by
    rw [← map_inv, thC_val, inv_inv]
  ext y
  rw [mem_img', mem_perp', mem_perp', hi]
  constructor
  · intro h x hx
    have := h (q.val *ᵥ x) ⟨x, hx, by rw [Matrix.toLin'_apply]⟩
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
    exact this
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    exact h x hx

theorem perpD_twConj (d q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perpD (starRingEnd ℂ) (twConj (thC n) q d) (img q⁻¹ W) =
      img q⁻¹ (perpD (starRingEnd ℂ) d W) := by
  rw [perpD, perpD, perp_img, ← img_mul, twConj, map_inv]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [img_mul]

theorem img_le_img (g : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') :
    img g W ≤ img g W' := Submodule.map_mono h

theorem img_ne_bot (g : GL (Fin n) ℂ) {W : Submodule ℂ (Fin n → ℂ)} (h : W ≠ ⊥) : img g W ≠ ⊥ := by
  intro h0
  apply h
  have : img g⁻¹ (img g W) = W := by rw [← img_mul, inv_mul_cancel, img_one]
  rw [← this, h0]
  exact Submodule.map_bot _

theorem conj_mem (p : GL (Fin n) ℂ) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) :
    p.val * X * (p⁻¹ : GL (Fin n) ℂ).val ∈ nilrad (img p W₁) (img p W₂) := by
  have hpp : ∀ y : Fin n → ℂ, (p⁻¹ : GL (Fin n) ℂ).val *ᵥ (p.val *ᵥ y) = y := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e : ∀ y : Fin n → ℂ, (p.val * X * (p⁻¹ : GL (Fin n) ℂ).val) *ᵥ y =
      p.val *ᵥ (X *ᵥ ((p⁻¹ : GL (Fin n) ℂ).val *ᵥ y)) := fun y => by
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [e, mem_img', hpp]
    exact hX.1 _
  · rw [mem_img'] at hy
    rw [e, mem_img', hpp]
    exact hX.2.1 _ hy
  · rw [mem_img'] at hy
    rw [e, hX.2.2 _ hy, Matrix.mulVec_zero]

theorem img_inv_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img q (img q⁻¹ W) = W := by
  rw [← img_mul, mul_inv_cancel, img_one]

def cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) := ⟨(q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val, by
    have := conj_mem q⁻¹ X.2
    rwa [inv_inv] at this⟩

def cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    nilrad W₁ W₂ := ⟨q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val, by
    have := conj_mem q Z.2
    rwa [img_inv_img, img_inv_img] at this⟩

theorem cnF_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (cnF q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem cnB_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    (cnB q W₁ W₂ Z).1 = q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val := rfl

theorem cnF_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X Y : nilrad W₁ W₂) :
    cnF q W₁ W₂ (X + Y) = cnF q W₁ W₂ X + cnF q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnF_val, mul_add, add_mul])

theorem cnB_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (X Y : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    cnB q W₁ W₂ (X + Y) = cnB q W₁ W₂ X + cnB q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnB_val, mul_add, add_mul])

theorem cnB_cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    cnB q W₁ W₂ (cnF q W₁ W₂ X) = X :=
  Subtype.ext (by
    have h1 : q.val * (q⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
    rw [cnB_val, cnF_val]
    calc _ = (q.val * (q⁻¹ : GL (Fin n) ℂ).val) * X.1 * (q.val * (q⁻¹ : GL (Fin n) ℂ).val) := by
          simp only [mul_assoc]
      _ = X.1 := by rw [h1]; simp)

theorem cnF_cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) : cnF q W₁ W₂ (cnB q W₁ W₂ Z) = Z :=
  Subtype.ext (by
    have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
    rw [cnF_val, cnB_val]
    calc _ = ((q⁻¹ : GL (Fin n) ℂ).val * q.val) * Z.1 * ((q⁻¹ : GL (Fin n) ℂ).val * q.val) := by
          simp only [mul_assoc]
      _ = Z.1 := by rw [h1]; simp)

def conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    nilrad W₁ W₂ ≃+ nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) :=
  AddMonoidHom.toAddEquiv (AddMonoidHom.mk' (cnF q W₁ W₂) (cnF_add q W₁ W₂))
    (AddMonoidHom.mk' (cnB q W₁ W₂) (cnB_add q W₁ W₂))
    (AddMonoidHom.ext fun X => cnB_cnF q W₁ W₂ X) (AddMonoidHom.ext fun Z => cnF_cnB q W₁ W₂ Z)
theorem conjNil_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (conjNil q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem continuous_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem continuous_conjNil_symm (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂).symm :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem uOf_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    uOf (conjNil q W₁ W₂ X) = q⁻¹ * uOf X * q := by
  apply Units.ext
  have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, conjNil_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem continuous_thC : Continuous (thC n) := by
  have hv : ∀ h : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ),
      Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := id
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).valᴴ :=
      (Units.continuous_val.comp continuous_inv).matrix_conjTranspose
    exact this.congr fun g => (thC_val g).symm
  · have : Continuous fun g : GL (Fin n) ℂ => (g : GL (Fin n) ℂ).valᴴ :=
      Units.continuous_val.matrix_conjTranspose
    refine this.congr fun g => ?_
    have : (((thC n g)⁻¹ : GL (Fin n) ℂ)).val = g.valᴴ := by
      rw [← map_inv, thC_val, inv_inv]
    exact this.symm

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Filtration

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

noncomputable def descend (f : π.IntertwiningMap σ) (B A : Subrepresentation π)
    (h : ∀ v ∈ A.toSubmodule, f v = 0) : (subQuot B A).IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (f.toLinearMap ∘ₗ B.toSubmodule.subtype) (fun v hv => h v.1 hv)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact f.isIntertwining _ _ g v.1

theorem vanish_step (f : π.IntertwiningMap σ) {A B : Subrepresentation π}
    (hA : ∀ v ∈ A.toSubmodule, f v = 0)
    (hz : ∀ φ : (subQuot B A).IntertwiningMap σ, φ.toLinearMap = 0) :
    ∀ v ∈ B.toSubmodule, f v = 0 := by
  intro v hv
  have h1 := LinearMap.congr_fun (hz (GlobalTheory.CompanionTheory.Filtration.descend f B A hA)) (Submodule.Quotient.mk ⟨v, hv⟩)
  have h2 : (GlobalTheory.CompanionTheory.Filtration.descend f B A hA).toLinearMap (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rw [← h2, h1, LinearMap.zero_apply]

theorem vanish_climb {N : ℕ} (S : Fin (N + 1) → Subrepresentation π) (f : π.IntertwiningMap σ)
    (lo : ℕ) (hlo : lo < N + 1)
    (h0 : ∀ v ∈ (S ⟨lo, hlo⟩).toSubmodule, f v = 0) (hi : ℕ) (hle : lo ≤ hi) :
    ∀ (hhi : hi < N + 1),
      (∀ t : Fin N, lo ≤ t.val → t.val < hi →
        ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
      ∀ v ∈ (S ⟨hi, hhi⟩).toSubmodule, f v = 0 := by
  induction hi, hle using Nat.le_induction with
  | base =>
    intro _ _
    exact h0
  | succ k hk ih =>
    intro hhi hz
    have hkN : k < N := Nat.lt_of_succ_lt_succ hhi
    have ih' := ih (Nat.lt_succ_of_lt hkN)
      (fun t h1 h2 => hz t h1 (Nat.lt_succ_of_lt h2))
    exact GlobalTheory.CompanionTheory.Filtration.vanish_step f
      (A := S (⟨k, hkN⟩ : Fin N).castSucc) (B := S (⟨k, hkN⟩ : Fin N).succ) ih'
      (hz ⟨k, hkN⟩ hk (Nat.lt_succ_self k))

theorem intertwining_proportional :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ)
      (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
      ∀ t₀ : Fin N,
        (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) →
        (∀ t : Fin N, t ≠ t₀ →
          ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
        ∀ φ ψ : π.IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  intro G V W _ _ _ _ _ π σ N S _ hS0 hST t₀ hmult hzero φ ψ
  have happ : ∀ (f : π.IntertwiningMap σ) (v : V), f.toLinearMap v = f v :=
    fun f v => Representation.IntertwiningMap.toLinearMap_apply π σ f v
  have hbot : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S ⟨0, Nat.succ_pos N⟩).toSubmodule, f v = 0 := by
    intro f v hv
    have e0 : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by
      first
        | exact Fin.mk_zero
        | exact Fin.ext (by simp)
    rw [e0, hS0] at hv
    have hv0 : v = 0 := by
      first
        | exact (Submodule.mem_bot ℂ).1 hv
        | exact hv
        | simpa using hv
        | exact (Submodule.mem_bot ℂ).1
            ((bot_le : (⊥ : Subrepresentation π) ≤
              ⟨⊥, fun g w hw => by rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩) hv)
    rw [hv0, ← happ, map_zero]
  have htop : ∀ v : V, v ∈ (S (Fin.last N)).toSubmodule := by
    intro v
    rw [hST]
    first
      | exact Submodule.mem_top
      | trivial
      | exact (le_top : (⟨⊤, fun _ _ _ => Submodule.mem_top⟩ : Subrepresentation π) ≤ ⊤)
          (Submodule.mem_top (x := v))
      | simp
  have hlow : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f =>
    GlobalTheory.CompanionTheory.Filtration.vanish_climb S f 0 (Nat.succ_pos N) (hbot f)
      t₀.val (Nat.zero_le _) (Nat.lt_succ_of_lt t₀.isLt)
      (fun t _ ht => hzero t (by rintro rfl; exact lt_irrefl _ ht))
  have hup : ∀ f : π.IntertwiningMap σ, (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → ∀ v, f v = 0 := by
    intro f hf v
    have h := GlobalTheory.CompanionTheory.Filtration.vanish_climb S f (t₀.val + 1)
      (Nat.succ_lt_succ t₀.isLt) hf N t₀.isLt (Nat.lt_succ_self N)
      (fun t h1 _ => hzero t (by rintro rfl; exact Nat.not_succ_le_self _ h1))
    exact h v (htop v)
  have hdesc : ∀ (f : π.IntertwiningMap σ) (hf : ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0) (v : V)
      (hv : v ∈ (S t₀.succ).toSubmodule),
      (GlobalTheory.CompanionTheory.Filtration.descend f (S t₀.succ) (S t₀.castSucc) hf).toLinearMap
        (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    intro f hf v hv
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rcases hmult (GlobalTheory.CompanionTheory.Filtration.descend φ (S t₀.succ) (S t₀.castSucc) (hlow φ))
      (GlobalTheory.CompanionTheory.Filtration.descend ψ (S t₀.succ) (S t₀.castSucc) (hlow ψ)) with h | ⟨c, hc⟩
  · left
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply, happ]
    refine hup φ ?_ v
    intro w hw
    rw [← hdesc φ (hlow φ) w hw, h, LinearMap.zero_apply]
  · right
    refine ⟨c, ?_⟩
    let χ : π.IntertwiningMap σ :=
      { toLinearMap := ψ.toLinearMap - c • φ.toLinearMap
        isIntertwining' := fun g => by
          first
            | rw [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.comp_smul,
                ψ.isIntertwining' g, φ.isIntertwining' g]
            | (ext v
               have h1 := LinearMap.congr_fun (ψ.isIntertwining' g) v
               have h2 := LinearMap.congr_fun (φ.isIntertwining' g) v
               simp only [LinearMap.comp_apply] at h1 h2
               simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2,
                 map_sub, map_smul]) }
    have hχ : ∀ v, χ v = ψ v - c • φ v := by
      intro v
      rw [← happ, ← happ, ← happ]
      rfl
    have hχS : ∀ v ∈ (S t₀.succ).toSubmodule, χ v = 0 := by
      intro v hv
      rw [hχ, ← hdesc ψ (hlow ψ) v hv, ← hdesc φ (hlow φ) v hv, hc, LinearMap.smul_apply, sub_self]
    apply LinearMap.ext
    intro v
    have h := hup χ hχS v
    rw [hχ, sub_eq_zero] at h
    rw [LinearMap.smul_apply, happ, happ]
    exact h

end GlobalTheory.CompanionTheory.Filtration
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevel
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatLevel

theorem exists_trivial_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : A) (y : M) (h : f • y = 0) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → M), y = ∑ j, u j • v j ∧ ∀ j, f * u j = 0 := by
  classical
  have h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0 := by simpa using h
  obtain ⟨n, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, fun j => a () j, z, ?_, fun j => ?_⟩
  · simpa using hx ()
  · simpa using ha j

theorem exists_mul_of_flat {W B : Type} [CommRing W] [CommRing B] {t : W} (ht : t ∈ nonZeroDivisors W)
    {a b m : ℕ} (h : a + b = m) (c : W ⧸ Ideal.span {t ^ m} →+* B) (hc : c.Flat) (y : B)
    (hy : c (Ideal.Quotient.mk _ (t ^ b)) * y = 0) : ∃ z, c (Ideal.Quotient.mk _ (t ^ a)) * z = y := by
  let _ := c.toAlgebra
  have : Module.Flat (W ⧸ Ideal.span {t ^ m}) B := hc
  have hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0 := by
    rw [Algebra.smul_def]
    exact hy
  obtain ⟨n, u, v, hyv, hu⟩ := exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb
  have key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s) := by
    intro j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u j)
    have h1 := hu j
    rw [← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, hs⟩ := h1
    refine ⟨s, ?_⟩
    rw [← hw]
    congr 1
    have hb' : t ^ b ∈ nonZeroDivisors W := pow_mem ht b
    have h2 : (w - t ^ a * s) * t ^ b = 0 := by
      rw [← h, pow_add] at hs
      linear_combination (-1 : W) * hs
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)
  choose s hs using key
  refine ⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩
  rw [hyv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]
  rfl

theorem natCast_mem_nonZeroDivisors (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    (l : WittVector l k) ∈ nonZeroDivisors (WittVector l k) := by
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

set_option backward.isDefEq.respectTransparency false in
theorem flatL_Kt : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  intro l _ k _ _ _ O _ F ρ m
  show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))
  rw [CrystallineSemistableComparison.Pb.LsG.modF_sW]
  intro i
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · funext s
    have h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change ((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})
      ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0
    rw [h0, map_zero, zero_mul]
  · have key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i,
        ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)),
          (l : WittVector l k) ^ a • z = x s := by
      intro s
      have hs : (s.obj (Fin.last i)).obj.i.Flat := (s.obj (Fin.last i)).property
      have h0 : (l : WittVector l k) ^ b • x s = 0 := congrFun hx s
      obtain ⟨z, hz⟩ := exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab
        (s.obj (Fin.last i)).obj.i hs (x s) h0
      exact ⟨z, hz⟩
    choose z hz using key
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    exact ⟨z, funext fun s => hz s⟩

end GlobalTheory.CompanionTheory.FlatLevel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_statement : PositivityTheory.RgDs.K.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | exact GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgKeyTransfer.transfer <;> assumption)
end

