module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNotMemDvdLocallyAway
section
open NumberField IsDedekindDomain Formalism.L2.Ker

namespace GlobalTheory

theorem exists_not_mem_dvd_locally_away (E : Type) [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ t : 𝓞 E, t ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q →
      ∃ w : 𝓞 E, w ∉ Q'.asIdeal ∧ ∃ z : 𝓞 E, w * t = r * z := by
  have hI : Ideal.span {r} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hnu : ¬ IsUnit Q.asIdeal := fun h => Q.isPrime.ne_top (Ideal.isUnit_iff.1 h)
  obtain ⟨J, hJ, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hI).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity Q.asIdeal (Ideal.span {r})
  have hJle : ¬ J ≤ Q.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htQ⟩ := Set.not_subset.1 hJle
  refine ⟨t, htQ, fun Q' hQ' => ?_⟩
  have hnle : ¬ Q.asIdeal ^ m ≤ Q'.asIdeal := by
    intro h
    have h1 : Q.asIdeal ≤ Q'.asIdeal := Q'.isPrime.le_of_pow_le h
    have h2 : Q.asIdeal = Q'.asIdeal := Q.isMaximal.eq_of_le Q'.isPrime.ne_top h1
    exact hQ' (HeightOneSpectrum.ext h2.symm)
  obtain ⟨w, hwm, hwQ'⟩ := Set.not_subset.1 hnle
  refine ⟨w, hwQ', ?_⟩
  have hmem : w * t ∈ Ideal.span {r} := by
    rw [hJ]; exact Ideal.mul_mem_mul hwm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨z, by rw [← hz, mul_comm]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.VolBridge

variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N)

def locHom : (Sp E N ≃ₗ[E] Sp E N) →* GL A k where
  toFun x := ⟨toLoc ι e e x.toLinearMap, toLoc ι e e (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap,
    by
      rw [← toLoc_comp_square]
      have h : x.toLinearMap ∘ₗ (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square],
    by
      rw [← toLoc_comp_square]
      have h : (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ x.toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square]⟩
  map_one' := by
    ext1
    show toLoc ι e e (LinearEquiv.refl E (Sp E N)).toLinearMap = 1
    exact toLoc_id_square ι e
  map_mul' x y := by
    ext1
    show toLoc ι e e (x * y).toLinearMap = toLoc ι e e x.toLinearMap * toLoc ι e e y.toLinearMap
    rw [← toLoc_comp_square]
    rfl

theorem locHom_val (x : Sp E N ≃ₗ[E] Sp E N) : (locHom ι e x).val = toLoc ι e e x.toLinearMap := rfl

section Num
variable {A : Type} {N c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (N + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = N + i.val)

include hcc he in
theorem eX_lt (a : A) : (e (Sum.inl a)).val < N := by
  by_contra h
  push Not at h
  have hc : (e (Sum.inl a)).val - N < c := by have := (e (Sum.inl a)).isLt; omega
  have h2 : e (Sum.inr ⟨_, hc⟩) = e (Sum.inl a) := Fin.ext (by rw [he]; simp; omega)
  exact absurd (e.injective h2) (by simp)

def eX : A ≃ Fin N :=
  Equiv.ofBijective (fun a => ⟨(e (Sum.inl a)).val, eX_lt e hcc he a⟩) (by
    constructor
    · intro a b hab
      have : e (Sum.inl a) = e (Sum.inl b) := Fin.ext (by simpa using congrArg Fin.val hab)
      simpa using e.injective this
    · intro m
      rcases hm : e.symm (Fin.castAdd c' m) with a | i
      · refine ⟨a, Fin.ext ?_⟩
        have := congrArg (fun z => (e z).val) hm
        simp at this
        simp [← this]
      · exfalso
        have := congrArg (fun z => (e z).val) hm
        simp [he] at this
        have := m.isLt
        omega)

theorem eX_val (a : A) : ((eX e hcc he a : Fin N) : ℕ) = (e (Sum.inl a)).val := rfl

end Num

section Ext
variable {E : Type} [Field E] {N c : ℕ}

def extX (c : ℕ) (y : Sp E N ≃ₗ[E] Sp E N) : Sp E (N + c) ≃ₗ[E] Sp E (N + c) :=
  (LinearEquiv.funCongrLeft E E finSumFinEquiv) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E) ≪≫ₗ
    (y.prodCongr (LinearEquiv.refl E (Fin c → E))) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft E E finSumFinEquiv).symm

theorem extX_castAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin N) :
    extX c y v (Fin.castAdd c i) = y (fun i => v (Fin.castAdd c i)) i := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]
  rfl

theorem extX_natAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin c) :
    extX c y v (Fin.natAdd N i) = v (Fin.natAdd N i) := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]

end Ext

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocal
section
open NumberField IsDedekindDomain Formalism.L2.Ker

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.CocIntLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem embH_apply (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ) (hs : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x))
    (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hs, Complex.conj_conj]
  ring

theorem int_of_local (M : Submodule (𝓞 E) (HomE E a b)) (f : HomE E a b → HomE E a b → ℝ)
    (hadd : ∀ x x' y, f (x + x') y = f x y + f x' y) (hsm : ∀ (r : E) x y, f (r • x) y = f x (star r • y))
    (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, f x y = n) (x y : HomE E a b)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal M ∧
      star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal M) : ∃ n : ℤ, f x y = n := by
  have hzero : ∀ z, f 0 z = 0 := fun z => by
    have := hadd 0 0 z
    rw [add_zero] at this
    linarith
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, f ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [hzero]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, hadd, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        show ∃ n : ℤ, f ((s * (c * r)) • x) y = n
        rw [← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨v, hv, hy⟩ := hy
    have hmem : u * cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := hM _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO E v)) • x = (star (algebraMap (𝓞 E) E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, hsm, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hP.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv ((mem_conjP Q v).2 h')
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

theorem integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  intro E _ _ _ ι _ _ a b emb δ d sc M _ hs hsd hsc x y h
  have hmemL : ∀ {z : HomE E a b}, z ∈ M → embH emb δ z ∈ laV emb δ M := fun {z} hz => ⟨z, hz, rfl⟩
  have hsmA : ∀ (r : E) (x y : HomE E a b), altE (HV sc) (embH emb δ (r • x)) (embH emb δ y) =
      altE (HV sc) (embH emb δ x) (embH emb δ (star r • y)) := by
    intro r x y; simp only [altE, hv_smul emb δ sc hs]
  have hintA : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, altE (HV sc) (embH emb δ x) (embH emb δ y) = n := by
    intro x hx y hy
    have h1 := hmemL hx
    rw [← hsd] at h1
    exact h1 _ (hmemL hy)
  refine ⟨int_of_local M (fun x y => altE (HV sc) (embH emb δ x) (embH emb δ y)) ?_ hsmA hintA x y h,
    int_of_local M (fun x y => (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re +
      altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2) ?_ ?_ ?_ x y h⟩
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im]
  · intro x x' y
    simp only [altE, map_add (f := _), LinearMap.add_apply, Complex.add_im, Complex.add_re]
    ring
  · intro r x y
    simp only [altE, hv_smul emb δ sc hs]
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hintA x hx y hy
    have h := hsc.2 _ (hmemL hx) _ (hmemL hy)
    simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n + m, ?_⟩
    have h2 := congrArg Complex.im hn
    have h3 : (HV sc (embH emb δ y) (embH emb δ x)).re = (HV sc (embH emb δ x) (embH emb δ y)).re := by
      rw [hv_swap]; simp
    simp only [altE] at hm
    simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, altE, hm] at h2
    simp at h2
    simp only [altE, hm]
    push_cast
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith

end GlobalTheory.CocIntLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := _root_.GlobalTheory.SymBridge.ComplRes.residues E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPoint
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem GlobalTheory.symLevel_lam_residue_elim : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  exact GlobalTheory.symLevel_lam_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
end

