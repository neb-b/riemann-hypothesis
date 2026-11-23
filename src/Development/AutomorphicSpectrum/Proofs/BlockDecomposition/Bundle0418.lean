module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Fib

section Abstract

variable {G D W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
  [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_translate (H : Subgroup G) (σ : Representation ℂ H W)
    (f : smoothPart (ind H σ)) (e : D → G) (he : Continuous e) (h0 : e 0 = 1)
    (hadd : ∀ a b, e (a + b) = e a * e b) (y : G) :
    IsLocallyConstant (fun d => f.1.1 (e d * y)) := by
  have hK : IsOpen {g : G | ind H σ g f.1 = f.1} := f.2
  let c : D → G := fun a => y⁻¹ * e a * y
  have hc : Continuous c := by fun_prop
  have hU : IsOpen (c ⁻¹' {g : G | ind H σ g f.1 = f.1}) := hK.preimage hc
  rw [IsLocallyConstant.iff_exists_open]
  intro d
  refine ⟨(fun x => -d + x) ⁻¹' (c ⁻¹' {g : G | ind H σ g f.1 = f.1}), hU.preimage (by fun_prop), ?_, ?_⟩
  · show ind H σ (c (-d + d)) f.1 = f.1
    simp [c, h0]
  · intro x hx
    have hx' : ind H σ (c (-d + x)) f.1 = f.1 := hx
    have h1 : e x = e d * e (-d + x) := by rw [← hadd, add_neg_cancel_left]
    have h2 := congrArg (fun v : indSpace H σ => v.1 (e d * y)) hx'
    have h3 : (ind H σ (c (-d + x)) f.1).1 (e d * y) = f.1.1 (e d * y * c (-d + x)) := rfl
    simp only [h3] at h2
    have h4 : e d * y * c (-d + x) = e x * y := by
      simp only [c, h1]; group
    simpa [h4] using h2

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp [dEmb, this]

theorem dEmb_add (i t : ℕ) (a b : Fin (t + 1) → k) : dEmb k i t (a + b) = dEmb k i t a * dEmb k i t b := by
  apply Subtype.ext
  have : Fin.append (0 : Fin (i + 1) → k) (a + b) = Fin.append (0 : Fin (i + 1) → k) a + Fin.append (0 : Fin (i + 1) → k) b := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [dEmb, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  have hcol : Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
    refine continuous_matrix fun r c => ?_
    by_cases hc : c = Fin.last _
    · subst hc
      refine Fin.lastCases ?_ (fun r' => ?_) r
      · simpa [colMat] using continuous_const
      · simp only [colMat, if_true, Fin.lastCases_castSucc]
        refine Fin.addCases (fun a => ?_) (fun a => ?_) r'
        · simpa using continuous_const
        · simpa using continuous_apply a
    · simpa [colMat, hc] using continuous_const
  constructor
  · exact continuous_const.add hcol
  · exact continuous_const.sub hcol

theorem dEmb_mul_entry (i t : ℕ) (d : Fin (t + 1) → k) (g : Mir k ((i + 1) + t + 1)) (b : Fin (t + 1)) :
    (((dEmb k i t d * g : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) =
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) + d b := by
  have hg : ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun ((mem_Mir_iff k _).1 g.2) (Fin.last _)
    simpa [eLast] using this
  have hv : ((dEmb k i t d : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl
  have hc : colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = d b := by
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right]
  rw [Subgroup.coe_mul, Units.val_mul, hv, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last _)]
  · rw [hc]
    exact congrArg (_ + ·) ((congrArg (d b * ·) hg).trans (mul_one _))
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem hpg_entry_eq_zero (i t : ℕ) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (b : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _) = 0 := by
  have h1 := mem_parab_iff.1 (show ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k)) ∈ parab k (ePG (i + 1) (t + 1)) from hh)
    true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_false_last] at h1
  have h2 : ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
    apply Fin.ext
    rw [ePG_true_val]
    simp
  rw [h2] at h1
  exact h1

theorem fibre_isLocallyConstant_hasCompactSupport (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
      HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  refine ⟨isLocallyConstant_translate (HPG k (i + 1) (t + 1)) (sigX τ σ) f.1 (dEmb k i t) (continuous_dEmb i t)
    (dEmb_zero i t) (dEmb_add i t) y, ?_⟩
  obtain ⟨C, hC, hf⟩ := f.2
  let φ : Mir k ((i + 1) + t + 1) → Fin (t + 1) → k := fun c b =>
    -(((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) b)) (Fin.last _)
  have hφ : Continuous φ := by
    refine continuous_pi fun b => Continuous.neg ?_
    have h1 : Continuous fun c : Mir k ((i + 1) + t + 1) =>
        (((y * c⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
          Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_inv))
    exact (continuous_apply_apply _ _).comp h1
  refine HasCompactSupport.intro (hC.image hφ) fun x hx => ?_
  by_contra hne
  obtain ⟨h, hh, c, hc, e⟩ := hf (dEmb k i t x * y) hne
  refine hx ⟨c, hc, ?_⟩
  have e1 : h = dEmb k i t x * (y * c⁻¹) := by
    rw [← mul_assoc]
    exact eq_mul_inv_of_mul_eq e.symm
  funext b
  have h0 := hpg_entry_eq_zero i t h hh b
  rw [e1, dEmb_mul_entry] at h0
  exact neg_eq_of_add_eq_zero_right h0

end GlobalTheory.CompanionTheory.BZPhiPG.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.AdelEqProof

theorem map_thetaR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  change f (σ ((g⁻¹ : GL (Fin n) A).val j i)) = τ (((GeneralLinearGroup.map f g)⁻¹ : GL (Fin n) B).val j i)
  rw [← map_inv]
  exact h _

theorem map_PhiU {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n A) = PhiU n B := by
  apply Units.ext
  ext i j
  change f ((PhiU n A).val i j) = (PhiU n B).val i j
  rw [phiU_val, phiU_val]
  simp [GlobalTheory.Tw.Phi, apply_ite f]

theorem map_thetaGL {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaGL n σ g) = thetaGL n τ (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_PhiU, map_thetaR f σ τ h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

theorem pFin_conjAd (x : Ad E) :
    pFin E (conjAd E x) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E x) := rfl

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) :
    cV v (conjAd E x) = starRingEnd ℂ (cV v x) := by
  have h : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) := by
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) ((infEq E).symm x.1))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change pInf E (conjAd E x) v = _
  rw [h]
  rfl

theorem cV_algebraMap (v : InfinitePlace E) (y : E) : cV v (algebraMap E (Ad E) y) = v.embedding y :=
  pInf_algebraMap y v

theorem map_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = GeneralLinearGroup.map v.embedding d := by
  apply Units.ext
  ext i j
  exact cV_algebraMap v _

theorem map_pFin_ratGL (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  apply Units.ext
  ext i j
  rfl

theorem map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  apply Units.ext
  ext i j
  rfl

theorem map_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) :=
  map_thetaGL _ _ _ pFin_conjAd n g

theorem map_cV_twConj (v : InfinitePlace E) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (twConj (thetaA E n) x (ratGL E n d)) =
      twConj (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map (cV v) x) (GeneralLinearGroup.map v.embedding d) := by
  simp only [twConj, map_mul, map_inv, map_cV_ratGL]
  rw [map_thetaR (cV v) (conjAd E) (starRingEnd ℂ) (cV_conjAd v) n x]

theorem map_pFin_twConj (hT : TranslAd) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := hT E n u hu x
  have h2 : twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹ =
      x⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) x := by
    rw [h, map_mul, map_inv]
    simp only [twConj]
    group
  rw [h2, map_mul, map_mul, map_inv, map_pFin_ratGL, map_pFin_thetaGL]

theorem cpt_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x)) := by
  rw [cpt, map_cW, map_pFin_twConj hT u hu]

theorem cpt'_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt' w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w) (thF E n
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x))) := by
  rw [cpt', map_cW, map_pFin_thetaGL, map_pFin_twConj hT u hu]

theorem adelEqOf : AdelEqOf := by
  intro hT E _ _ _ a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [adel, orbFn, finFn]
  refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun v _ => ?_)
    (finprod_congr fun w => finprod_congr fun _ => ?_)
  · rw [map_cV_twConj, map_cV_twConj]
    rfl
  · rw [cpt_twConj hT w u₁ h₁, cpt_twConj hT w u₂ h₂, cpt'_twConj hT w u₁ h₁, cpt'_twConj hT w u₂ h₂]
    rfl

end GlobalTheory.CompanionTheory.AdelEqProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL PositivityTheory.Rg.Cz
open scoped Classical

namespace GlobalTheory.CompanionTheory.FrameCasimir

theorem sum_embeddings {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : Type} [AddCommMonoid N]
    (f : (E →+* ℂ) → N) :
    ∑ τ, f τ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : v.embedding ≠ ComplexEmbedding.conjugate v.embedding := by
    intro h
    have hc : v.IsComplex := IsTotallyComplex.isComplex v
    exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (star_star τ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

theorem atEmb_embedding {E : Type} [Field E] (v : InfinitePlace E) (z : ℂ) :
    atEmb v.embedding z = (Pi.single v z : Cinf E) := by
  unfold atEmb
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  congr 1 <;> simp

theorem map_single_atEmb {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (φ : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    φ (toL (Matrix.single i j (atEmb τ z))) =
      z • cx τ φ i j + starRingEnd ℂ z • cx (ComplexEmbedding.conjugate τ) φ i j := by
  let L : Cinf E →ₗ[ℝ] N :=
    { toFun := fun x => φ (toL (Matrix.single i j x))
      map_add' := fun x y => by
        rw [Matrix.single_add]
        exact φ.map_add _ _
      map_smul' := fun r x => by
        rw [← Matrix.smul_single]
        exact φ.map_smul r _ }
  have hL : ∀ x, φ (toL (Matrix.single i j x)) = L x := fun _ => rfl
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [hL, atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [cx, hL, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  have h1 := Complex.add_conj z
  have h2 := Complex.sub_conj z
  push_cast at h1 h2
  match_scalars
  · simp only [Complex.coe_algebraMap]; linear_combination (-1 / 2 : ℂ) * h1
  · simp only [Complex.coe_algebraMap]; linear_combination (Complex.I / 2 : ℂ) * h2 + z.im * Complex.I_mul_I

theorem alg_sq {R : Type} [Ring R] [Algebra ℂ R] (u w : R) :
    (u + w) * (u + w) - (Complex.I • u - Complex.I • w) * (Complex.I • u - Complex.I • w) =
      (2 : ℂ) • (u * u) + (2 : ℂ) • (w * w) := by
  rw [← smul_sub, smul_mul_smul_comm, Complex.I_mul_I]
  simp only [mul_add, add_mul, sub_mul, mul_sub]
  module

theorem alg_sum {R : Type} [Ring R] [Algebra ℂ R] {a : ℕ} (P : Fin a → Fin a → R) (c d : ℂ)
    (h0 : c * c + d * d = 0) (h1 : 2 * (c * d) = 1) :
    ∑ i, ∑ j, (c • P i j + d • P j i) * (c • P i j + d • P j i) = ∑ i, ∑ j, P i j * P j i := by
  have e : ∀ i j, (c • P i j + d • P j i) * (c • P i j + d • P j i) =
      (c * c) • (P i j * P i j) + (c * d) • (P i j * P j i) + (c * d) • (P j i * P i j) + (d * d) • (P j i * P j i) := by
    intro i j
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    module
  simp only [e, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun i j => P j i * P i j), Finset.sum_comm (f := fun i j => P j i * P j i)]
  generalize (∑ i, ∑ j, P i j * P i j) = S
  generalize (∑ i, ∑ j, P i j * P j i) = T
  calc (c * c) • S + (c * d) • T + (c * d) • T + (d * d) • S = (c * c + d * d) • S + (2 * (c * d)) • T := by module
    _ = T := by rw [h0, h1, zero_smul, one_smul, zero_add]

theorem iM_single {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) (z : ℂ) :
    iM (Matrix.single i j (Pi.single v z : Cinf E)) = Matrix.single i j (Pi.single v (Complex.I * z) : Cinf E) := by
  unfold iM
  rw [Matrix.smul_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.single_eq_of_ne hw]

theorem fr_val {E : Type} [Field E] {a : ℕ} (v : InfinitePlace E) (i j : Fin a) :
    (fr (v, i, j) : Herm E a).1 = Matrix.single i j (Pi.single v ((1 + Complex.I) / 2) : Cinf E) +
      Matrix.single j i (Pi.single v (starRingEnd ℂ ((1 + Complex.I) / 2)) : Cinf E) := by
  change frU (v, i, j) + star (frU (v, i, j)) = _
  congr 1
  unfold frU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw
    simp only [Pi.star_apply, Pi.single_eq_same, Complex.star_def]
  · simp [Pi.single_eq_of_ne hw]

theorem frameCas : FrameCas := by
  intro E _ _ _ a M _ _ _ _ φ
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hc0 : c * c + starRingEnd ℂ c * starRingEnd ℂ c = 0 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
  have hc1 : 2 * (c * starRingEnd ℂ c) = 1 := by
    simp only [hc, map_div₀, map_add (f := _), map_one, Complex.conj_I, map_ofNat]
    ring_nf
    simp
    norm_num
  let P : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx v.embedding φ
  let Q : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v => cx (ComplexEmbedding.conjugate v.embedding) φ
  let u : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => c • P v i j + starRingEnd ℂ c • P v j i
  let w : InfinitePlace E → Fin a → Fin a → Module.End ℂ M := fun v i j => starRingEnd ℂ c • Q v i j + c • Q v j i
  have hs : ∀ v i j z, φ (toL (Matrix.single i j (Pi.single v z : Cinf E))) = z • P v i j + starRingEnd ℂ z • Q v i j := by
    intro v i j z
    rw [← atEmb_embedding]
    exact map_single_atEmb φ v.embedding i j z
  have hadd : ∀ A B : Matrix (Fin a) (Fin a) (Cinf E), φ (toL (A + B)) = φ (toL A) + φ (toL B) :=
    fun A B => φ.map_add (toL A) (toL B)
  have hfr : ∀ v i j, φ (toL (fr (v, i, j) : Herm E a).1) = u v i j + w v i j := by
    intro v i j
    rw [fr_val, hadd, hs, hs, Complex.conj_conj]
    simp only [u, w]
    abel
  have hiM : ∀ v i j, φ (toL (iM (fr (v, i, j) : Herm E a).1)) = Complex.I • u v i j - Complex.I • w v i j := by
    intro v i j
    have e : iM ((fr (v, i, j) : Herm E a).1) = iM (Matrix.single i j (Pi.single v c : Cinf E)) +
        iM (Matrix.single j i (Pi.single v (starRingEnd ℂ c) : Cinf E)) := by
      rw [fr_val]
      exact smul_add _ _ _
    rw [e, iM_single, iM_single, hadd, hs, hs]
    simp only [u, w, map_mul, Complex.conj_I, Complex.conj_conj]
    module
  have L1 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (fr k : Herm E a).1) * φ (toL (fr k : Herm E a).1) =
      ∑ v, ∑ i, ∑ j, (u v i j + w v i j) * (u v i j + w v i j) := by
    simp only [Fintype.sum_prod_type, hfr]
  have L2 : ∑ k : InfinitePlace E × Fin a × Fin a, φ (toL (iM (fr k : Herm E a).1)) * φ (toL (iM (fr k : Herm E a).1)) =
      ∑ v, ∑ i, ∑ j, (Complex.I • u v i j - Complex.I • w v i j) * (Complex.I • u v i j - Complex.I • w v i j) := by
    simp only [Fintype.sum_prod_type, hiM]
  rw [L1, L2, sum_embeddings, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu : ∑ i, ∑ j, u v i j * u v i j = ∑ i, ∑ j, P v i j * P v j i :=
    alg_sum (P v) c (starRingEnd ℂ c) hc0 hc1
  have hw : ∑ i, ∑ j, w v i j * w v i j = ∑ i, ∑ j, Q v i j * Q v j i :=
    alg_sum (Q v) (starRingEnd ℂ c) c (by rw [add_comm]; exact hc0) (by rw [mul_comm (starRingEnd ℂ c)]; exact hc1)
  change _ = (2 : ℂ) • (∑ i, ∑ j, P v i j * P v j i + ∑ i, ∑ j, Q v i j * Q v j i)
  rw [← hu, ← hw, smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => alg_sq _ _

end GlobalTheory.CompanionTheory.FrameCasimir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, ite_eq_right hc,
    ite_eq_right hrc, add_zero]

theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  apply one_add_colMat_apply_eq_zero_of_ne_last k (m + j) _
    (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a)
  intro h
  have h' := congrArg Fin.val h
  rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val,
    GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
  have ha := a.isLt
  omega

end GlobalTheory.CompanionTheory.LeibPhi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdealStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_lowering_pow_mem_ideal : ∀ {n : ℕ} (i j : Fin n) (x : U n), (j : ℕ) = i + 1 → ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | exact GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent | (intros; apply GlobalTheory.CompanionTheory.PresRho.lower_locally_nilpotent <;> assumption)
end

