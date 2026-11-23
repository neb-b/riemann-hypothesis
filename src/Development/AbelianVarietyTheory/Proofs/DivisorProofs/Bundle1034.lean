module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractions
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply _root_.GlobalTheory.EtC.hInv_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact _root_.GlobalTheory.EtC.hInv_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact _root_.GlobalTheory.EtC.hInv_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.ExpFrame Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

def ofOL (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l :=
  (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

def IntegralBlock (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ) : Prop :=
  ∃ (LL : FinExt l) (r : G E Ω →* GL (Fin n) ↥(OL LL)) (ψ : Fin t → G E Ω →* (↥(OL LL))ˣ) (ϖ : ↥(OL LL))
    (R : ℕ) (M : Fin (R + 1) → Submodule ↥(OL LL) (Fin n → ↥(OL LL))) (rs : Fin t → Fin R),
    (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧
    CrysWith ((Matrix.GeneralLinearGroup.map (ofOL l LL)).comp r) (fun τ => Finset.univ.val.map (J τ)) ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 ((Units.map (ofOL l LL).toMonoidHom).comp (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    Irreducible ϖ ∧ (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → ↥(OL LL), x = fun a => ϖ * y a) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧
    (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x ∈ M k) ∧
    Function.Injective rs ∧
    ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧
      M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span ↥(OL LL) {x} ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x - (fun a => ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) * x a) ∈
        M (rs s).castSucc

end Galois

section Reduced

variable {F : Type} [Field F] {n : ℕ}

def lau (y : Fin n → F⟦X⟧) : Fin n → LaurentSeries F := fun a => ((y a : F⟦X⟧) : LaurentSeries F)

def phiV (l : ℕ) (P : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  P.mulVec fun a => frob0 l (y a)

def gamV (un : F⟦X⟧) (D : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  (1 + (X : F⟦X⟧) • D).mulVec fun a => gam0 0 un (y a)

def RedFilt {ι : Type} (σ : Equiv.Perm ι) (l : ℕ) {t : ℕ} (un : F⟦X⟧) (P D : ι → Matrix (Fin n) (Fin n) F⟦X⟧)
    (Pψ Dψ : Fin t → ι → F⟦X⟧) : Prop :=
  ∃ (R : ℕ) (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (rs : Fin t → Fin R)
    (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
    Function.Injective rs ∧
    (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
    (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
    (∀ i k y, lau y ∈ V (σ i) k → lau (phiV l (P i) y) ∈ V i k) ∧
    (∀ i k y, lau y ∈ V i k → lau (gamV un (D i) y) ∈ V i k) ∧
    (∀ i s, lau (e i s) ∉ V i (rs s).castSucc ∧
      V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {lau (e i s)}) ∧
    (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (phiV l (P i) (e (σ i) s)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : LaurentSeries F)) •
          lau (e i s) ∈ V i (rs s).castSucc) ∧
    ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (gamV un (D i) (e i s)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i : F⟦X⟧) : LaurentSeries F)) • lau (e i s) ∈ V i (rs s).castSucc

end Reduced

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL


omit [DecidableEq O] in
theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring


open Classical in
theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
  simp

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
end
end

