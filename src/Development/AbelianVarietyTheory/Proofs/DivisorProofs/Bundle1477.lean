module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfEqZero
section
set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_congr (x : Ainf p O) : ∃ z, frobenius x = x ^ p + (p : Ainf p O) * z := by
  have h : frobenius x - x ^ p ∈ Ideal.span {(p : Ainf p O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, coeff_frobenius_charP, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨y, by linear_combination -hy⟩

theorem frob_teich (r : PreTilt O p) :
    frobenius (teichmuller p r : Ainf p O) = teichmuller p (r ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

theorem frob_nu (ε : PreTilt O p) : frobenius (nu ε) = mu ε := by
  rw [nu, mu, map_sub, map_one, frob_teich, root, frobeniusEquiv_symm_pow_p]

theorem frob_mu (ε : PreTilt O p) : frobenius (mu ε) = mu ε * frobenius (xi ε) := by
  rw [show frobenius (mu ε) = frobenius (xi ε * nu ε) by rw [xi_mul_nu], map_mul, frob_nu,
    mul_comm]

theorem frob_xi (ε : PreTilt O p) : ∃ d, frobenius (xi ε) = p + mu ε * d := by
  have h : frobenius (xi ε) = ∑ i ∈ Finset.range p, (teichmuller p ε : Ainf p O) ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [xi, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, frob_teich, root, frobeniusEquiv_symm_pow_p]
  have hd : ∀ i : ℕ, mu ε ∣ (teichmuller p ε : Ainf p O) ^ i - 1 := fun i => by
    rw [mu]; simpa using sub_dvd_pow_sub_pow (teichmuller p ε : Ainf p O) 1 i
  choose d hd using hd
  refine ⟨∑ i ∈ Finset.range p, d i, ?_⟩
  rw [h, Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => hd i]
  simp [Finset.sum_sub_distrib]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (mu ε) = 0 := by
  rw [mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

variable (ε : PreTilt O p)

def rel : Ideal (Ainf p O)[X] := Ideal.span {C (p : Ainf p O) * X - C (mu ε), X ^ 2}

abbrev BR : Type := (Ainf p O)[X] ⧸ rel ε

def a : Ainf p O →+* BR ε := (Ideal.Quotient.mk (rel ε)).comp C

def τ : BR ε := Ideal.Quotient.mk (rel ε) X

theorem p_τ : (p : BR ε) * τ ε = a ε (mu ε) := by
  rw [τ, a, RingHom.comp_apply, ← map_natCast (Ideal.Quotient.mk (rel ε)), ← map_mul,
    ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_natCast C]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem τ_sq : τ ε * τ ε = 0 := by
  rw [τ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem a_natCast (n : ℕ) : a ε n = n := map_natCast _ n

def θ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : BR ε →+* O :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom (fontaineTheta O p) 0) (fun f hf => by
    have h : rel ε ≤ RingHom.ker (eval₂RingHom (fontaineTheta O p) 0) := by
      refine Ideal.span_le.2 ?_
      rintro g (rfl | rfl) <;> simp [theta_mu hε]
    exact (RingHom.mem_ker).1 (h hf))

theorem θ_a {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    θ hε (a ε x) = fontaineTheta O p x := by
  rw [θ, a, RingHom.comp_apply, Ideal.Quotient.lift_mk]; simp

theorem θ_τ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : θ hε (τ ε) = 0 := by
  rw [θ, τ, Ideal.Quotient.lift_mk]; simp

def σ : BR ε →+* BR ε :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom ((a ε).comp frobenius) (τ ε * a ε (frobenius (xi ε))))
    (fun f hf => by
      have h : rel ε ≤ RingHom.ker (eval₂RingHom ((a ε).comp frobenius)
          (τ ε * a ε (frobenius (xi ε)))) := by
        refine Ideal.span_le.2 ?_
        rintro g (rfl | rfl)
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_sub, eval₂_mul,
            eval₂_C, eval₂_X, eval₂_natCast, RingHom.comp_apply, map_natCast]
          rw [frob_mu, map_mul, ← p_τ]; ring
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_X_pow]
          rw [mul_pow, sq (τ ε), τ_sq, zero_mul]
      exact (RingHom.mem_ker).1 (h hf))

theorem σ_a (x : Ainf p O) : σ ε (a ε x) = a ε (frobenius x) := by
  simp [σ, a, Ideal.Quotient.lift_mk]

theorem σ_τ : σ ε (τ ε) = τ ε * a ε (frobenius (xi ε)) := by
  simp [σ, τ, Ideal.Quotient.lift_mk]

abbrev BQ : Type := Localization.Away (p : BR ε)

def s : BQ ε →+* BQ ε :=
  IsLocalization.map (M := Submonoid.powers (p : BR ε)) (T := Submonoid.powers (p : BR ε))
    (BQ ε) (σ ε) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by rw [map_pow, map_natCast]⟩)

theorem s_alg (b : BR ε) : s ε (algebraMap (BR ε) (BQ ε) b) = algebraMap (BR ε) (BQ ε) (σ ε b) :=
  IsLocalization.map_eq _ _

theorem gen (b : BR ε) : ∃ x y, b = a ε x + τ ε * a ε y := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f.coeff 0, f.divX.coeff 0, ?_⟩
  have h1 := divX_mul_X_add f
  have h2 := divX_mul_X_add f.divX
  have hX : Ideal.Quotient.mk (rel ε) (X ^ 2) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  conv_lhs => rw [← h1, ← h2]
  simp only [map_add (f := _), map_mul, a, τ, RingHom.comp_apply]
  have : Ideal.Quotient.mk (rel ε) f.divX.divX * Ideal.Quotient.mk (rel ε) X *
      Ideal.Quotient.mk (rel ε) X = 0 := by
    rw [mul_assoc, ← map_mul, ← sq, hX, mul_zero]
  linear_combination this

section Faithful

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (root ε).untilt p := by
  simpa [zeta] using hε 1

theorem eps_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : ε - 1 ≠ 0 := by
  rw [← GlobalTheory.MuDivides.constantCoeff_mu, WittVector.constantCoeff_apply]
  exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).1

theorem mu_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : mu ε ≠ 0 :=
  (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).2.1

theorem mu_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w :=
  GlobalTheory.MuDivides.dvd_of_dvd_p_mul hv ε (eps_ne hv hε) w h

theorem mu_sq_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * w) : mu ε ^ 2 ∣ w := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨w', rfl⟩ := mu_dvd hv hε w (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  rw [sq, mul_left_comm] at h
  rw [sq]
  exact mul_dvd_mul_left _ (mu_dvd hv hε w' ((mul_dvd_mul_iff_left (mu_ne hv hε)).1 h))

theorem dvd_of_eq_zero (x y : Ainf p O) (h : a ε x + τ ε * a ε y = 0) :
    mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y := by
  have hm : C x + C y * X ∈ rel ε := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h, map_add (f := _), map_mul, mul_comm]; rfl
  obtain ⟨h1, h2, he⟩ := Ideal.mem_span_pair.1 hm
  have he' : C x + C y * X = h1 * C (p : Ainf p O) * X - h1 * C (mu ε) + h2 * X ^ 2 := by
    rw [← he]; ring
  have e0 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) he'
  have e1 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) he'
  simp only [coeff_add, coeff_sub, coeff_C_zero, coeff_mul_X_zero, coeff_mul_C,
    coeff_mul_X_pow', coeff_C_succ] at e0 e1
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X, coeff_mul_X, coeff_mul_C, coeff_C_zero] at e1
  simp only [coeff_C_succ, zero_add, Nat.one_lt_ofNat, if_neg (by norm_num : ¬ (2 ≤ 1)),
    if_neg (by norm_num : ¬ (2 ≤ 0)), add_zero, zero_sub] at e0 e1
  refine ⟨-(h1.coeff 1), ?_⟩
  rw [e0, e1]; ring

theorem eq_zero_of_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x y : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y) : a ε x + τ ε * a ε y = 0 := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨z, hz⟩ := h
  obtain ⟨x', rfl⟩ := mu_dvd hv hε x ⟨-y + mu ε * z, by linear_combination hz⟩
  have hy : y = mu ε * z - p * x' := by
    have : mu ε * (y - (mu ε * z - p * x')) = 0 := by linear_combination hz
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mu_ne hv hε))
  subst hy
  have h1 := p_τ ε
  have h2 := τ_sq ε
  simp only [map_mul, map_sub, map_natCast]
  rw [← h1]
  linear_combination (↑p * a ε z) * h2

theorem torsion_free (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (b : BR ε)
    (h : (p : BR ε) * b = 0) : b = 0 := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  refine eq_zero_of_dvd hv hε x y (mu_sq_dvd hv hε _ ?_)
  have := dvd_of_eq_zero (ε := ε) (p * x) (p * y) (by
    rw [map_mul, map_mul, a_natCast]; linear_combination h)
  rw [show (p : Ainf p O) * (p * x + mu ε * y) = p * (p * x) + mu ε * (p * y) by ring]
  exact this

end Faithful

end GlobalTheory.BRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFrames
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchCoords


open GlobalTheory.FockVacuum in
theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_cplx_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSigna
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ArchCoordsD


open GlobalTheory.FockVacuum in
theorem herm_rot_pos {ι : Type} [Fintype ι] {P Q R S : ι → ℕ} (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b *
      star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star ((fun w => Matrix.of fun a b => lineSign a b * Complex.I * c w a b :
        ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith


open GlobalTheory.FockVacuum in
theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C hCM hFr
  have hU := fun c : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  have hi : Function.Injective (p.prod q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := herm_rot_pos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : q c = 0 := congrArg Prod.snd hc
    rw [← hω, h1, h2] at h
    simp at h
  obtain ⟨θ, φ₀, hp, hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords (GlobalTheory.ArchUniq.trP F κ)
    (GlobalTheory.ArchUniq.Coord.isPairing_trP κ) _ rfl
  refine ⟨_, θ, (LinearEquiv.ofBijective (p.prod q) ⟨hi, hs⟩).trans φ₀, φ₀, hp, hq, fun c c' => ?_, fun u c hu hc => ?_⟩
  · change GlobalTheory.RealWeil.sympl (φ₀ (p c, q c)) (φ₀ (p c', q c')) = _
    rw [GlobalTheory.RealWeil.sympl, hp, hp, real_inner_comm, hq, hq]
    have h := hω c c'
    change GlobalTheory.ArchUniq.trP F κ (p c) (q c') - GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _ at h
    change -GlobalTheory.ArchUniq.trP F κ (p c) (q c') - -GlobalTheory.ArchUniq.trP F κ (p c') (q c) = _
    linarith
  · rw [hU' _ u ⟨hu, hc⟩]
    rfl

end GlobalTheory.ArchCoordsD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] (V V' : ValuationSubring Ω), IsAbove R K V.toSubring → IsAbove R K V'.toSubring → ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  first | exact @GlobalTheory.ValConj.exists_smul_eq_of_isAbove | exact GlobalTheory.ValConj.exists_smul_eq_of_isAbove | (intros; apply GlobalTheory.ValConj.exists_smul_eq_of_isAbove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSectionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ellipticCharpoly_compact_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinChar.finite_ell_charpoly | exact GlobalTheory.FinChar.finite_ell_charpoly | (intros; apply GlobalTheory.FinChar.finite_ell_charpoly <;> assumption)
end

