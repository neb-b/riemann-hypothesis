module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem cd_red (N M₀ : ℕ) [NeZero (N * M₀)] (a : ℤ) :
    (((a : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = (a : ZMod M₀) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast (dvd_mul_left M₀ N)]

private theorem cd_div (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (k : ℤ) :
    ((((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ)) : ZMod M₀) = (k : ZMod M₀) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : (((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ℤ) = k % (M₀ : ℤ) := by
    rw [Int.natCast_div, ZMod.val_intCast, Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ hN,
      Int.mul_ediv_cancel_left _ hN.ne']
  rw [← Int.cast_natCast, h1, ZMod.intCast_mod]

private theorem cd_int (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (h h' : Matrix (Fin 2) (Fin 2) ℤ)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) :
    cD N M₀ (h.map (Int.castRingHom (ZMod (N * M₀)))) = h'.map (Int.castRingHom (ZMod M₀)) := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one]
    at e00 e01 e10 e11
  have f00 : h 0 0 = h' 0 0 := mul_left_cancel₀ hN (e00.trans (mul_comm _ _))
  have f10 : h 1 0 = (N : ℤ) * h' 1 0 := e10.trans (mul_comm _ _)
  ext i j
  fin_cases i <;> fin_cases j
  · show ((((h 0 0 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 0 : ℤ) : ZMod M₀)
    rw [cd_red, f00]
  · show ((N * ((h 0 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 1 : ℤ) : ZMod M₀)
    rw [Nat.cast_mul, cd_red, ← e01, Int.cast_mul, Int.cast_natCast]
  · show ((((h 1 0 : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ZMod M₀) = ((h' 1 0 : ℤ) : ZMod M₀)
    rw [f10, cd_div]
  · show ((((h 1 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 1 1 : ℤ) : ZMod M₀)
    rw [cd_red, e11]

private theorem cd_lift (N M : ℕ) [NeZero M] (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hm : ((m 1 0).val : ZMod N) = 0) :
    ∃ h h' : Matrix (Fin 2) (Fin 2) ℤ, h.map (Int.castRingHom (ZMod M)) = m ∧
      !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hm
  refine ⟨m.map fun a => (a.val : ℤ),
    !![((m 0 0).val : ℤ), N * ((m 0 1).val : ℤ); (k : ℤ), ((m 1 1).val : ℤ)], ?_, ?_⟩
  · ext i j
    show (((m i j).val : ℤ) : ZMod M) = m i j
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hk' : ((m 1 0).val : ℤ) = (k : ℤ) * N := by rw [hk]; push_cast; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one,
        Matrix.map_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, hk', mul_comm]

private theorem cd_mul (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (m m' : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0) :
    cD N M₀ (m * m') = cD N M₀ m * cD N M₀ m' := by
  obtain ⟨a, a', rfl, ha⟩ := cd_lift N _ m hm
  obtain ⟨b, b', rfl, hb⟩ := cd_lift N _ m' hm'
  have hab : !![(N : ℤ), 0; 0, 1] * (a * b) = (a' * b') * !![(N : ℤ), 0; 0, 1] := by
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  rw [← Matrix.map_mul, cd_int N M₀ _ _ hab, cd_int N M₀ _ _ ha, cd_int N M₀ _ _ hb, Matrix.map_mul]

private theorem cd_one (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] :
    cD N M₀ (1 : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) = 1 := by
  have h := cd_int N M₀ 1 1 (by rw [Matrix.mul_one, Matrix.one_mul])
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)] at h

private theorem cd_inv (N M₀ : ℕ) [NeZero (N * M₀)] (m n : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (e : n * m = 1) (hm : ((m 1 0).val : ZMod N) = 0) : ((n 1 0).val : ZMod N) = 0 := by
  let φ := ZMod.castHom (dvd_mul_right N M₀) (ZMod N)
  have hφ : ∀ a : ZMod (N * M₀), ((a.val : ℕ) : ZMod N) = φ a := fun a => by
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [hφ] at hm ⊢
  have e0 := congrArg φ (congrFun (congrFun e 0) 0)
  have e1 := congrArg φ (congrFun (congrFun e 1) 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul, map_mul, hm] at e0 e1
  rw [Matrix.one_apply_eq, map_one] at e0
  rw [Matrix.one_apply_ne (by decide), map_zero] at e1
  linear_combination φ (n 0 0) * e1 - φ (n 1 0) * e0

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCdFacts :
    UpperTheory.V.Z.Kato.Nb.SCdFacts := by
  intro N M₀ M _ _ _ hM
  subst hM
  refine ⟨cd_mul N M₀, cd_one N M₀, ?_, cd_int N M₀⟩
  intro m hm x y hxy
  have hn := cd_inv N M₀ _ _ m.inv_mul hm
  have key : ∀ z : Row M₀, (2 : ZMod M₀) • z ≠ 0 →
      (2 : ZMod M₀) • (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) ≠ 0 := by
    intro z hz h0
    apply hz
    have h1 := congrArg (fun v => v ᵥ* cD N M₀ ((m⁻¹ : GL (Fin 2) (ZMod (N * M₀))) :
      Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) h0
    simp only [Matrix.zero_vecMul] at h1
    rwa [Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← cd_mul N M₀ _ _ hm hn, m.mul_inv, cd_one,
      Matrix.vecMul_one] at h1
  exact ⟨key x hxy.1, key y hxy.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

private theorem coeQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  unfold toGQ
  rw [dite_eq_left h]
  rfl

private theorem mulQ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by
    rw [Matrix.det_mul]
    exact mul_pos h h'
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coeQ _ hmm, coeQ _ h, coeQ _ h', Matrix.map_mul]

private theorem slQ (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext
  apply Units.ext
  rw [coeQ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)]
  rfl

private theorem detD {N : ℕ} (hN : 0 < N) : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1]).det := by
  simpa [Matrix.det_fin_two_of] using hN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_zero : eOm ε 0 = 1 := by
  simp only [eOm, Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

private theorem coeff_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (f : X.K) (r : ℚ) :
    (X.exp (slD X N f)).coeff r = (X.exp f).coeff (r / N) := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hg : (((toGQ !![(N : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(N : ℚ), 0; 0, 1] := by
    rw [coeQ _ (detD hN)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, hg]
  have h00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, hg]
  have h01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, hg]
  have h11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, hg]
  have key := X.exp_upper _ h10 f (r / N)
  rw [h00, h01, h11, div_one, div_one, mul_zero, div_mul_cancel₀ _ hN', eOm_zero, one_mul] at key
  exact key

private theorem gal_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (slD X N f) = slD X N (X.gal s f) := by
  apply X.exp.toRingHom.injective
  ext r
  change (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, coeff_slD X hN, coeff_slD X hN, X.gal_exp]

private theorem sl_slD (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hh : 0 < h.det)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (f : X.K) :
    X.sl (toGQ h) (slD X N f) = slD X N (X.sl (toGQ h') f) := by
  have hD := detD hN
  have hh' : 0 < h'.det := by
    have key := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_mul] at key
    exact (mul_pos_iff_of_pos_right hD).1 (key ▸ mul_pos hD hh)
  unfold slD
  rw [← X.sl_mul, ← X.sl_mul, ← mulQ _ _ hD hh, ← mulQ _ _ hh' hD, e]

private theorem un_group (X : Tower Ω ε) (m : ℕ) :
    1 ∈ X.Un m ∧ ∀ f ∈ X.Un m, ∀ f' ∈ X.Un m, f * f' ∈ X.Un m ∧ f⁻¹ ∈ X.Un m := by
  refine ⟨fun W _ => ⟨1, by simp⟩, fun f hf f' hf' => ⟨fun W hW => ?_, fun W hW => ?_⟩⟩
  · obtain ⟨g, hg⟩ := hf W hW
    obtain ⟨g', hg'⟩ := hf' W hW
    refine ⟨g * g', ?_⟩
    have key : ((f * f' : X.Kˣ) : X.K) / ((g * g' : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m) * ((f' : X.K) / (g' : X.K) ^ m) := by
      rw [Units.val_mul, Units.val_mul]
      ring
    rw [key, map_mul, hg, hg', one_mul]
  · obtain ⟨g, hg⟩ := hf W hW
    refine ⟨g⁻¹, ?_⟩
    have key : ((f⁻¹ : X.Kˣ) : X.K) / ((g⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (g : X.K) ^ m)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div]
      simp only [inv_pow, div_inv_eq_mul]
      ring
    rw [key, map_inv₀, hg, inv_one]

variable [IsAlgClosure ℚ Ω]

private theorem exPrim (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne M)⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 (NeZero.pos M)).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.1 hζ⟩

private theorem uniq (M : ℕ) [NeZero M] (a b : ℕ) (h : ∀ z : Ω, z ^ M = 1 → z ^ a = z ^ b) :
    (a : ZMod M) = b := by
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨M, NeZero.pos M, hζ.pow_eq_one⟩
  have key := hfin.pow_eq_pow_iff_modEq.1 (h ζ hζ.pow_eq_one)
  rw [← hζ.eq_orderOf] at key
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 key

private theorem cyc_app (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (hz : z ^ M = 1) :
    s z = z ^ (cycM M s : ZMod M).val := by
  refine cycM_spec M s ?_ z hz
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  have hcop : i.Coprime M := (hζ.pow_iff_coprime (NeZero.pos M) i).1 (hi' ▸ hsζ)
  refine ⟨ZMod.unitOfCoprime i hcop, fun w hw => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, map_pow, ← hi', ← pow_mul, ← pow_mul, mul_comm]

private theorem cyc_eq (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (a : ℕ) (h : ∀ z : Ω, z ^ M = 1 → s z = z ^ a) :
    (cycM M s : ZMod M) = a := by
  have key := uniq (Ω := Ω) M (cycM M s : ZMod M).val a (fun z hz => by rw [← cyc_app M s z hz, h z hz])
  rwa [ZMod.natCast_zmod_val] at key

private theorem rep_app (M : ℕ) [NeZero M] (y : (ZMod M)ˣ) (z : Ω) (hz : z ^ M = 1) :
    repM (Ω := Ω) M y z = z ^ (y : ZMod M).val := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨ζ, hζ⟩ := exPrim (Ω := Ω) M
  have hm : ∀ {ξ : Ω}, IsPrimitiveRoot ξ M → Polynomial.cyclotomic M ℚ = minpoly ℚ ξ := fun hξ =>
    minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
      (by rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
          exact hξ.isRoot_cyclotomic (NeZero.pos M)) (Polynomial.cyclotomic.monic M ℚ)
  obtain ⟨s, hs⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1
    ((hm (hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime y))).symm.trans (hm hζ))
  have hs' : s ζ = ζ ^ (y : ZMod M).val := hs
  refine repM_spec M y ⟨s, fun w hw => ?_⟩ z hz
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
  rw [map_pow, hs', ← pow_mul, ← pow_mul, mul_comm]

end UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients

open UpperTheory.V.Z.Kato.Nb.SymmetricSquareCoefficients in
theorem UpperTheory.V.Z.Kato.Nb.sSlD :
    UpperTheory.V.Z.Kato.Nb.SSlD := by
  intro Ω _ _ _ ε X N hN
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  have hover := _root_.GlobalTheory.KZ.Tower.overY_comap_sl_gal ε X ε.injective ⟨φ, hφ2, hφ1⟩
  refine ⟨fun s f => gal_slD X hN s f, fun h h' hh e f => sl_slD X hN h h' hh e f, slQ,
    fun h h' hh hh' => mulQ h h' hh hh', fun m q f hf => ?_, fun m s f hf => ?_, un_group X, fun M _ s => ?_⟩
  · exact KmapA.un_map X (X.sl q).toRingEquiv (fun W hW => (hover W hW).1 q) m f hf
  · exact KmapA.un_map X (X.gal s) (fun W hW => (hover W hW).2 s) m f hf
  refine ⟨?_, fun t => ?_, fun y => ?_, ?_, fun M' _ hM' => ?_⟩
  · have hspec : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := fun z hz => cyc_app M s z hz
    have heps : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cyc M s).val := by
      unfold cyc
      exact Classical.epsilon_spec (p := fun y : ZMod M => ∀ z : Ω, z ^ M = 1 → s z = z ^ y.val) ⟨_, hspec⟩
    have key := uniq (Ω := Ω) M (cyc M s).val (cycM M s : ZMod M).val (fun z hz => by rw [← heps z hz, hspec z hz])
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at key
  · apply Units.ext
    rw [Units.val_mul, cyc_eq M (s * t) ((cycM M s : ZMod M).val * (cycM M t : ZMod M).val)
      (fun z hz => by rw [AlgEquiv.mul_apply, cyc_app M t z hz, map_pow, cyc_app M s z hz, ← pow_mul]),
      Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · apply Units.ext
    rw [cyc_eq M (repM M y) (y : ZMod M).val (fun z hz => rep_app M y z hz), ZMod.natCast_zmod_val]
  · rw [mem_fixMu_iff]
    constructor
    · intro hs
      apply Units.ext
      rw [cyc_eq M s 1 (fun z hz => by rw [pow_one]; exact hs z hz), Nat.cast_one, Units.val_one]
    · intro hs z hz
      rw [cyc_app M s z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod]
      have key : z ^ (1 % M) = z ^ 1 := by
        conv_rhs => rw [← Nat.mod_add_div 1 M]
        rw [pow_add, pow_mul, hz, one_pow, mul_one]
      rw [key, pow_one]
  · apply Units.ext
    rw [Units.coe_map, cyc_eq M' s (cycM M s : ZMod M).val
      (fun z hz => cyc_app M s z (by obtain ⟨k, hk⟩ := hM'; rw [hk, pow_mul, hz, one_pow]))]
    simp [ZMod.castHom_apply, ZMod.natCast_val]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem diam_ex (N l p : ℕ) (h : Nat.Coprime p (l * N)) : IsDiam N l p (sgD N l p) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) ((l * N : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  refine Classical.epsilon_spec (p := IsDiam N l p)
    ⟨⟨!![a, -b; ((l * N : ℕ) : ℤ), (p : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;> refine CongruenceSubgroup.Gamma0_mem.mpr ?_ <;>
      show (Int.cast ((l * N : ℕ) : ℤ) : ZMod _) = 0 <;> simp
  · simp [en]

private theorem conj_mem (N l : ℕ) (σ γ : SL(2, ℤ))
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (hγ : γ ∈ Gam N l) :
    σ * γ * σ⁻¹ ∈ Gam N l := by
  obtain ⟨hN, hl⟩ := Subgroup.mem_inf.mp hσ
  rw [CongruenceSubgroup.Gamma0_mem] at hN hl
  have h1 : (N : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hN
  have h2 : (l : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hl
  have h4 : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hP := StabHecke.congruenceCondition_of_mem hγ
  have hg : ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = σ 1 0 * γ 0 0 + σ 1 1 * γ 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine StabHecke.mem_Gam_of_mul N l _ _ _ hg h1 h2 (StabHecke.isCoprime_of_det h4 h1)
    (StabHecke.isCoprime_of_det h4 h2) ?_ ?_ ?_
  · rw [e00, show σ 0 0 * γ 0 0 + σ 0 1 * γ 1 0 - σ 0 0 = σ 0 0 * (γ 0 0 - 1) + σ 0 1 * γ 1 0 by ring]
    exact dvd_add (dvd_mul_of_dvd_right hP.1 _) (dvd_mul_of_dvd_right hP.2.1 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right hP.2.1 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right hP.2.2.1 _)

theorem UpperTheory.V.Z.Kato.Nb.sBStab :
    UpperTheory.V.Z.Kato.Nb.SBStab := by
  intro Ω _ _ _ ε X l _ N w hN b hb
  obtain ⟨hA, hG⟩ := _root_.GlobalTheory.KZ.kmap_A_stable ε X ε.injective (X.j_hol.imp fun _ h => h.symm) l
  have key : ∀ f : X.Fn l →ₗ[ℤ_[l]] X.Fn l, (∀ c ∈ X.BSet N l w, f c ∈ X.BSet N l w) → f b ∈ X.B N l w := by
    intro f hf
    have hle : X.B N l w ≤ (X.B N l w).comap f :=
      Submodule.span_le.mpr fun x hx => Submodule.subset_span (hf x hx)
    exact hle hb
  have hdet : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  refine ⟨fun s => key _ fun c hc => ⟨StabGal.galB_mem_Pol X l w s (hG s) c hc.1,
    fun γ hγ => StabGal.inv_galB X N l w hN s c hc γ hγ⟩, fun σ hσ => key _ fun c hc => ?_,
    fun p hp hc' => key _ fun c hc => ?_⟩
  · refine ⟨StabHecke.polAct X l w _ (hA _) c hc.1, fun γ hγ => ?_⟩
    have hg : (σ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((σ * γ * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [StabHecke.act_act X l _ _ (hdet γ) (hdet σ), hg, ← StabHecke.act_act X l _ _ (hdet σ) (hdet _),
      hc.2 _ (conj_mem N l σ γ hσ hγ)]
  · have hσ := diam_ex N l p hc'
    have hpl : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.coprime_mul_right_right hc')
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [StabHecke.heckeT_eq]
      exact StabHecke.Pol_sum X l w _ _ fun o _ => StabHecke.polAct X l w _ (hA _) c hc.1
    · rw [StabHecke.heckeT_eq]
      exact StabHecke.sum_act_inv X l N (StabHecke.repT p (sgD N l p))
        (fun o => by rw [StabHecke.det_repT]; exact_mod_cast hp.pos) γ
        (StabHecke.map_T hp hσ hpl γ hγ) (StabHecke.coset_representatives_hecke_disjoint hp _) c hc.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Nb

def SEsLev : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), 1 ≤ N →
    ∀ b ∈ X.BSet N l w, ∀ n : ℕ, (∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      AdicCompletion.eval (idl l) (X.Kl l) n (b u - b u') = 0) ∧ (∀ (t : ℤ_[l]) u, b (t • u) = t ^ w • b u) ∧
      ∀ u, ∃ (k : ℕ) (F : X.Kˣ), n ≤ k ∧ F ∈ X.Un (l ^ n) ∧ ES.Lev X (6 * l * N * l ^ k) (F : X.K) ∧ Rep X l n F ((4 : ℤ_[l]) • b u)

def SEsFrob : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω),
    (normV v).Prime → normV v ≠ l → IsPlaceOver B v → IsFrob B (normV v) σ →
      FrobV B (normV v) σ ∧ (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = (normV v : ℕ)

def SEsT : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w q M : ℕ), 1 ≤ N →
    q.Prime → Nat.Coprime q (l * N) → Nat.Coprime q M → l * N ∣ M → ∀ γ : SL(2, ℤ), DiagMod M q γ → ∀ b ∈ X.BSet N l w,
      X.heckeT N l q b = (∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b) +
        X.act l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b ∧
      ∀ s, X.diam N l q (X.galB l s b) = X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b)

def SEs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), l ≠ 2 → ∀ (N w : ℕ),
    1 ≤ N → ∃ S0 : Finset ℕ, ∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S0 → (normV v).Prime →
      IsPlaceOver B v → IsFrob B (normV v) σ → ∀ b ∈ X.B N l w,
        X.heckeT N l (normV v) b = X.galB l σ b + ((normV v : ℤ_[l]) ^ (w + 1)) • X.diam N l (normV v) (X.galB l σ⁻¹ b)

end UpperTheory.V.Z.Kato.Nb

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sCls : SCls := by
  intro Ω _ _ _ ε X l _ n
  obtain ⟨hsurj, hinj, hmul, hone, hsmul, hmap, hsucc⟩ := H3.cls_props Ω ε X l n
  have hdiv : ∀ f f' : X.Kˣ, X.cls l n (f / f') = X.cls l n f - X.cls l n f' := by
    intro f f'
    have h := hmul (f / f') f'
    rw [div_mul_cancel] at h
    rw [h]
    abel
  have hpow : ∀ (f : X.Kˣ) (k : ℕ), X.cls l n (f ^ k) = k • X.cls l n f := by
    intro f k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, hmul, ih, succ_nsmul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hf : (f : X.K) ≠ 0 := f.ne_zero
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (clsK X l n (f : X.K)) = X.cls l n f
    unfold clsK
    rw [dite_eq_left hf, Units.mk0_val]
    unfold liftK
    exact Classical.epsilon_spec (p := fun b => (AdicCompletion.eval (idl l) (X.Kl l) n) b = X.cls l n f)
      (AdicCompletion.eval_surjective (idl l) (X.Kl l) n (X.cls l n f))
  · intro f f' a a' ha ha'
    refine ⟨?_, ?_⟩
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a + a') = X.cls l n (f * f')
      rw [map_add (f := _), hmul]
      rw [ha, ha']
    · show (AdicCompletion.eval (idl l) (X.Kl l) n) (a - a') = X.cls l n (f / f')
      rw [map_sub, hdiv]
      rw [ha, ha']
  · intro f a k ha
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ k)
    rw [map_nsmul, hpow]
    rw [ha]
  · intro f f' a a' ha ha' hc
    obtain ⟨g, hg⟩ := hc
    rw [map_sub]
    rw [ha, ha', (hinj f f').2 ⟨g, hg⟩, sub_self]
  · intro φ f a ha
    exact hmap φ a f ha
  · intro f a ha
    exact hsucc a f ha
  · intro f k a ha
    refine ⟨((PadicInt.toZModPow n) k).val, ?_⟩
    show (AdicCompletion.eval (idl l) (X.Kl l) n) (k • a) = X.cls l n (f ^ ((PadicInt.toZModPow n) k).val)
    rw [map_smul]
    rw [ha, hsmul]

end UpperTheory.V.Z.Kato.Nb

end
end

