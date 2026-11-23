module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def diagInf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : E →+* Cinf E :=
  (pInf E).comp (algebraMap E (Ad E))

theorem infDiag_eq (k : Eˣ) : infDiag k = infId E (Units.map (diagInf E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - infEq E 1 + infEq E ((infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

theorem denseRange_diagInf : DenseRange (diagInf E) := by
  have hc : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

theorem denseRange_units : DenseRange (Units.map (diagInf E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagInf.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem coord_expU (τ : E →+* ℂ) (x : Cinf E) : coord τ (expU x : (Cinf E)ˣ) = Complex.exp (coord τ x) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm


omit [NumberField E] in
theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))


open Classical in
theorem coord_atEmb' (σ τ : E →+* ℂ) (z : ℂ) : coord σ (atEmb τ z) =
    (if σ = τ then z else 0) + (if σ = ComplexEmbedding.conjugate τ then starRingEnd ℂ z else 0) := by
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (conj_ne σ).symm, add_zero, coord_atEmb]
  by_cases h2 : σ = ComplexEmbedding.conjugate τ
  · subst h2
    rw [if_neg h1, if_pos rfl, zero_add]
    have := atEmb_conj τ (starRingEnd ℂ z)
    rw [Complex.conj_conj] at this
    rw [← this, coord_atEmb]
  · have h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext; simp)
    rw [if_neg h1, if_neg h2, add_zero]
    unfold coord atEmb
    by_cases h3 : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h3]; simp [h]
    · rw [if_neg h3]; simp [h]

theorem chiInf_eq (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ i, f i (coord (φ i) u) := by
  refine congrFun (denseRange_units.equalizer (g := fun u => ((chiInf χ u : ℂˣ) : ℂ))
    (h := fun u : (Cinf E)ˣ => ∏ i, f i (coord (φ i) u)) (Units.continuous_val.comp (continuous_chiInf χ))
    (continuous_finsetProd _ fun i _ => continuous_iff_continuousAt.2 fun v => ?_) (funext fun k => ?_)) u
  · exact ContinuousAt.comp (g := f i) (f := fun u : (Cinf E)ˣ => coord (φ i) u)
      (hf i _ (v.isUnit.map (coord (φ i))).ne_zero)
      ((continuous_coord (φ i)).comp Units.continuous_val).continuousAt
  · have e := h k
    simp only [← coord_algebraMap (φ _) (k : E)] at e
    rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq] at e
    exact e


open Classical in
theorem expo_eq_sum (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ) (a b : I → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (he : ∀ i z, f i (Complex.exp z) = Complex.exp (a i * z + b i * starRingEnd ℂ z))
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (τ : E →+* ℂ) :
    expo χ τ = ∑ i, ((if φ i = τ then a i else 0) + (if φ i = ComplexEmbedding.conjugate τ then b i else 0)) := by
  refine expo_eq_of_exp χ τ _
    (∑ i, ((if φ i = τ then b i else 0) + (if φ i = ComplexEmbedding.conjugate τ then a i else 0))) fun z => ?_
  rw [chiInf_eq χ φ f hf h]
  simp only [coord_expU, he, coord_atEmb']
  rw [← Complex.exp_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp <;> ring

theorem expo_of_infType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  intro E _ _ _ χ
  classical
  refine ⟨fun n h τ => ?_, fun s h τ => ?_, fun I _ φ n hφ h i => ?_⟩
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => z ^ n σ) (fun σ => n σ) (fun _ => 0)
      (fun σ z hz => continuousAt_zpow₀ z _ (Or.inl hz)) (fun σ z => by simp [Complex.exp_int_mul]) h τ]
    simp
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun _ => s / 2) (fun _ => s / 2)
      (fun σ z hz => ?_) (fun σ z => ?_) h.2.2 τ]
    · simp [Finset.sum_add_distrib]
    · refine ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const ?_
      exact Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz)
    · rw [← Complex.ofReal_cpow (norm_nonneg _), Complex.norm_exp, ← Real.exp_mul, Complex.ofReal_exp]
      congr 1
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
  · have key := expo_eq_sum χ φ (fun i z => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (fun i => n i / 2) (fun i => -(n i : ℂ) / 2)
      (fun i z hz => ?_) (fun i z => ?_) h
    · have h1 : ∀ j, φ j = φ i ↔ j = i := fun j =>
        ⟨fun e => hφ (congrArg InfinitePlace.mk e), fun e => by rw [e]⟩
      have h2 : ∀ j, φ j ≠ ComplexEmbedding.conjugate (φ i) := fun j e => by
        have : j = i := hφ ((congrArg InfinitePlace.mk e).trans (InfinitePlace.mk_conjugate_eq _))
        subst this
        exact conj_ne _ e.symm
      have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ i)) = φ i := by ext; simp
      rw [key, key]
      simp [h1, h2, h3]
    · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
      exact (continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn).zpow₀ _
        (Or.inl (div_ne_zero hz hn))
    · rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
      congr 1
      have := Complex.add_conj z
      push_cast at this
      linear_combination ((n i : ℂ) / 2) * this

end GlobalTheory.CuspRep.InfType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.SignatureFactor

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem exists_factor : ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → p + q = M ∧ (∃ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G) ∧ ∀ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G → ∃ B : Matrix (Fin M) (Fin p ⊕ Fin q) ℂ, A * B = 1 ∧ B * A = 1 := by
  intro M p q G h
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e G) * P.val = Formalism.UG.Jpq p q := hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Units.val (P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) with hQ
  have hPQ : P.val * Q = 1 := by
    rw [hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG' : Qᴴ * Formalism.UG.Jpq p q * Q = reindex e e G := by
    rw [← hP']
    calc Qᴴ * (P.valᴴ * (reindex e e G) * P.val) * Q
        = (P.val * Q)ᴴ * (reindex e e G) * (P.val * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  have hdet : G.det ≠ 0 := by
    intro h0
    have h1 : (Formalism.UG.Jpq p q).det = 0 := by
      rw [← hP', Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, h0]; simp
    have h2 := congrArg Matrix.det (Jpq_mul_self p q)
    rw [Matrix.det_mul, h1] at h2
    simp at h2
  refine ⟨?_, ⟨Q.submatrix id e, ?_⟩, ?_⟩
  · simpa using (Fintype.card_congr e).symm
  · ext i j
    have := congrFun (congrFun hG' (e i)) (e j)
    simpa [Matrix.mul_apply] using this
  · intro A hA
    have hBA : (G⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by
      rw [Matrix.mul_assoc, hA]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨_, (Matrix.mul_eq_one_comm_of_equiv e).mp hBA, hBA⟩

end GlobalTheory.Mem.SignatureFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePaths
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

namespace GlobalTheory

theorem inertPath_card_eq_natCard {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P) (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hf : f.1.f = d.1.f) (hbe : f.1.be = d.1.be) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      Nat.card {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun e => ⟨e.1.1.N, e.1.2.lat, e.1.2.uni, ?_, ?_⟩
      invFun := fun Y => ⟨⟨{ N := Y.1, f := d.1.f, be := d.1.be },
          d.2.replN Y.2.1 Y.2.2.1 (fun R => hi_sameAt_inert (hST R) Y.2.2.2.1)
            (fun w => hi_sameAt_inert (hSG w) Y.2.2.2.1)⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := (Finset.mem_filter.1 e.2).1
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · have h := (Finset.mem_filter.1 e.2).2
    rw [DecoSet.mem_inertNb P.ne_bot] at h
    exact h.1
  · refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.1, rfl, rfl⟩
    · rw [DecoSet.mem_inertNb P.ne_bot]
      exact ⟨Y.2.2.2.2, hf, hbe⟩
  · intro e
    have h := Finset.mem_filter.1 e.2
    rw [DecoSet.mem_inertNb P.ne_bot, DecoSet.mem_inertNb P.ne_bot] at h
    exact Subtype.ext (Subtype.ext (Deco.ext rfl h.1.2.1.symm h.1.2.2.symm))
  · intro Y
    rfl

theorem inertPath_card_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (s t : List ℕ)
    (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : ¬ (f.1.f = d.1.f ∧ f.1.be = d.1.be)) :
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hfe
  rw [DecoSet.mem_inertNb P.ne_bot] at he hfe
  exact h ⟨hfe.2.1.trans he.2.1, hfe.2.2.trans he.2.2⟩

theorem inertPath_card_comm : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  intro E _ _ _ n P ST SG hST hSG s t d f ⟨φ⟩
  by_cases hdec : f.1.f = d.1.f ∧ f.1.be = d.1.be
  · rw [inertPath_card_eq_natCard P hST hSG s t d f hdec.1 hdec.2,
      inertPath_card_eq_natCard P hST hSG t s d f hdec.1 hdec.2]
    exact Nat.card_congr φ
  · rw [inertPath_card_eq_zero P s t d f hdec, inertPath_card_eq_zero P t s d f hdec]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrredOfCharpolyEq
section
open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.BrauerNesbittIrr

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

abbrev matHom (ρ : Γ →* GL (Fin a) k) : Γ →* Matrix (Fin a) (Fin a) k := (Units.coeHom _).comp ρ

abbrev liftRep (ρ : Γ →* GL (Fin a) k) : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin a) (Fin a) k :=
  MonoidAlgebra.lift k (Matrix (Fin a) (Fin a) k) Γ (matHom ρ)

theorem liftRep_mem (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) (α : MonoidAlgebra k Γ) :
    ∀ x ∈ W, liftRep ρ α *ᵥ x ∈ W := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => intro x _; simp [W.zero_mem]
  | add p q hp hq => intro x hx; rw [map_add (f := _), add_mulVec]; exact W.add_mem (hp x hx) (hq x hx)
  | single g c =>
    intro x hx
    rw [MonoidAlgebra.lift_single, Matrix.smul_mulVec]
    exact W.smul_mem c (hW g x hx)

theorem liftRep_surjective [IsAlgClosed k] (ρ : Γ →* GL (Fin a) k) (ha : 0 < a)
    (h : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective (liftRep ρ) := by
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hirr : IsIrrSub ρ ⊤ := ⟨top_ne_bot, fun g v _ => Submodule.mem_top,
    fun W' _ hinv => h W' hinv⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ hirr
  intro X
  have hle : Submodule.span k (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) ≤
      LinearMap.range (liftRep ρ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by simp⟩
  obtain ⟨α, hα⟩ := hle (hs ▸ Submodule.mem_top : X ∈ _)
  exact ⟨α, hα⟩

theorem irred_of_charpoly_eq [IsAlgClosed k] (ρ ρ' : Γ →* GL (Fin a) k)
    (hc : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ' g : Matrix (Fin a) (Fin a) k).charpoly)
    (h' : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ' g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hcp : ∀ α, (liftRep ρ α).charpoly = (liftRep ρ' α).charpoly :=
    GlobalTheory.charpoly_lift_eq_of_charpoly_eq a (matHom ρ) (matHom ρ') hc
  have hdet : ∀ α, (liftRep ρ α).det = (liftRep ρ' α).det := fun α => by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, hcp]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; exact absurd (Subsingleton.elim w 0) hw0
    · exact h
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hsurj := liftRep_surjective ρ' ha h'
  let S : Set (Matrix (Fin a) (Fin a) k) :=
    {X | ∃ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) ∧ liftRep ρ' α = X}
  let I : TwoSidedIdeal (Matrix (Fin a) (Fin a) k) := TwoSidedIdeal.mk' S
    ⟨0, fun x _ => by simp, by simp⟩
    (by
      rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
      exact ⟨α + β, fun x hx => by rw [map_add (f := _), add_mulVec, hα x hx, hβ x hx, add_zero],
        map_add _ _ _⟩)
    (by
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨-α, fun x hx => by rw [map_neg, neg_mulVec, hα x hx, neg_zero], map_neg _ _⟩)
    (by
      rintro X _ ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj X
      exact ⟨β * α, fun x hx => by rw [map_mul, ← mulVec_mulVec, hα x hx, mulVec_zero],
        map_mul _ _ _⟩)
    (by
      rintro _ Y ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj Y
      exact ⟨α * β, fun x hx => by
        rw [map_mul, ← mulVec_mulVec, hα _ (liftRep_mem ρ W hW β x hx)], map_mul _ _ _⟩)
  have hmem : ∀ X, X ∈ I ↔ X ∈ S := fun X => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ X
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · have h0 : ∀ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) → liftRep ρ' α = 0 := fun α hα => by
      have : liftRep ρ' α ∈ I := (hmem _).2 ⟨α, hα, rfl⟩
      rw [hI] at this
      exact (TwoSidedIdeal.mem_bot _).1 this
    let ψ : MonoidAlgebra k Γ →ₗ[k] (Fin (Module.finrank k W) → Fin a → k) :=
      { toFun := fun α i => liftRep ρ α *ᵥ ((Module.finBasis k W i : W) : Fin a → k)
        map_add' := fun α β => by funext i; simp [add_mulVec]
        map_smul' := fun c α => by funext i; simp [Matrix.smul_mulVec] }
    have hker : LinearMap.ker ψ ≤ LinearMap.ker (liftRep ρ').toLinearMap := by
      intro α hα
      rw [LinearMap.mem_ker] at hα ⊢
      apply h0 α
      intro x hx
      have hf : (Matrix.toLin' (liftRep ρ α)).comp W.subtype = 0 :=
        (Module.finBasis k W).ext fun i => by
          have := congrFun hα i
          simpa [ψ] using this
      have := LinearMap.congr_fun hf ⟨x, hx⟩
      simpa using this
    have hrange : LinearMap.range (liftRep ρ').toLinearMap = ⊤ := LinearMap.range_eq_top.2 hsurj
    let q := (LinearMap.ker ψ).liftQ (liftRep ρ').toLinearMap hker
    have hq : LinearMap.range q = ⊤ := by rw [Submodule.range_liftQ, hrange]
    haveI : FiniteDimensional k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) :=
      LinearEquiv.finiteDimensional (ψ.quotKerEquivRange).symm
    have h1 : Module.finrank k (Matrix (Fin a) (Fin a) k) ≤
        Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) := by
      have := LinearMap.finrank_range_le q
      rwa [hq, finrank_top] at this
    have h2 : Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) ≤
        Module.finrank k W * a := by
      rw [ψ.quotKerEquivRange.finrank_eq]
      refine (Submodule.finrank_le _).trans (le_of_eq ?_)
      first
        | simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
        | rw [Module.finrank_pi_fintype]; simp
        | simp [Module.finrank_pi]
    have h3 : Module.finrank k W < a := by
      have := Submodule.finrank_lt ht
      simpa using this
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
    nlinarith
  · have h1 : (1 : Matrix (Fin a) (Fin a) k) ∈ I := by rw [hI]; exact TwoSidedIdeal.mem_top _
    obtain ⟨κ, hκ, hκ1⟩ := (hmem _).1 h1
    have h0 : (liftRep ρ κ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hκ w hw⟩
    rw [hdet, hκ1, det_one] at h0
    exact one_ne_zero h0

theorem litBNIrr (Γ : Type) [Group Γ] : LitBNIrr Γ := by
  intro ℓ _ a ρ ρ' hc h' W hW
  exact irred_of_charpoly_eq ρ ρ' hc (fun W hW => h' W fun g _ x hx => hW g x hx) W
    (fun g x hx => hW g (Subgroup.mem_top g) x hx)

end GlobalTheory.BrauerNesbittIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatCFullLattice
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem latC_full_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), ∃ L : Submodule (𝓞 E) (Fin W.rank → E), (L : Set (Fin W.rank → E)) = latC W ∧ L.FG ∧ Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ := by
  intro E _ _ _ W
  refine ⟨W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)), ?_, W.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    simp only [latC, SetLike.mem_coe, Submodule.mem_map, Set.mem_ofPred_eq]
    rw [← W.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, W.frame.equivFun.apply_symm_apply x⟩
  · have h : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      let U := Submodule.span E (W.L0 : Set W.V)
      change U = ⊤
      by_contra h
      let e : W.V ≃ₗ⋆[E] W.V :=
        (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
      let g : W.V →ₗ[E] Module.Dual E U :=
        (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
      have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : E) : a • e z ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : W.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : W.hT y (e z) = 0 := by
          have hh := W.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : E →ₗ[𝓞 E] W.L0 :=
        ((LinearMap.toSpanSingleton E _ (e z)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
      let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have : ((W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin W.rank → E)) :
        Set (Fin W.rank → E)) = W.frame.equivFun.toLinearMap '' (W.L0 : Set W.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.Mem.Vol
end

