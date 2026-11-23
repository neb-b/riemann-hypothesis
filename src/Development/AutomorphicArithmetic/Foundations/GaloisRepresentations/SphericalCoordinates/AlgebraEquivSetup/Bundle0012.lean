module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PJSurj
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

section Core
variable {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ}

private theorem mulG {ε : R} (he : ε * ε = ε) (A B : Matrix (Fin n) (Fin n) R) :
    ((1 - ε) • A + ε • (1 : Matrix (Fin n) (Fin n) R)) * ((1 - ε) • B + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      (1 - ε) • (A * B) + ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination he
  have h2 : (1 - ε) * ε = 0 := by linear_combination -he
  have h3 : ε * (1 - ε) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul, h1, h2, h3, he,
    zero_smul, add_zero, zero_add]

private theorem smul_eq_of_map (Φ : R →+* R') {ε : R} (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {M N : Matrix (Fin n) (Fin n) R} (h : M.map Φ = N.map Φ) : (1 - ε) • M = (1 - ε) • N := by
  ext i k
  have hik : Φ (M i k - N i k) = 0 := by
    have := congrFun (congrFun h i) k
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  have := hker _ hik
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination this

private theorem inv_part (Φ : R →+* R') {ε : R} (he : ε * ε = ε) (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' Y Y' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hYY : Y.map Φ * Y'.map Φ = 1) :
    ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) *
      ((1 - ε) • (a' * Y' * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  rw [mulG he]
  have h1 : (a' * Y * a * (a' * Y' * a)).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by
    have e : a' * Y * a * (a' * Y' * a) = a' * Y * (a * a') * Y' * a := by simp only [Matrix.mul_assoc]
    have hA : a'.map Φ * a.map Φ = 1 := by
      rw [← Matrix.map_mul, ha', Matrix.map_one _ (map_zero Φ) (map_one Φ)]
    rw [e, haa, Matrix.mul_one, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc (a'.map Φ), hYY,
      Matrix.mul_one, hA, Matrix.map_one _ (map_zero Φ) (map_one Φ)]
  rw [smul_eq_of_map Φ hker h1, ← add_smul, sub_add_cancel, one_smul]

private theorem star_part (Φ : R →+* R') (σ : R →+* R) (σ' : R' →+* R') {ε t : R}
    (hσ : ∀ x, Φ (σ x) = σ' (Φ x)) (he : ε * ε = ε) (hσe : σ ε = ε)
    (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' D Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hD : (a.map σ)ᵀ * D * a = 1)
    (hX : ((Y.map Φ).map σ')ᵀ * D.map Φ * Y.map Φ = Φ t • D.map Φ) :
    ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ *
      ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      ((1 - ε) * t + ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  have hGs : ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ =
      (1 - ε) • ((a' * Y * a).map σ)ᵀ + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i k
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hσe]
    rcases eq_or_ne i k with rfl | h
    · simp
    · simp [Matrix.one_apply, h, h.symm]
  rw [hGs, mulG he]
  have hab : (a'.map σ)ᵀ * (a.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, haa, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hDa : D * a = (a'.map σ)ᵀ := by
    have : (a'.map σ)ᵀ * ((a.map σ)ᵀ * D * a) = (a'.map σ)ᵀ := by rw [hD, Matrix.mul_one]
    rwa [Matrix.mul_assoc ((a.map σ)ᵀ), ← Matrix.mul_assoc, hab, Matrix.one_mul] at this
  have hD2 : (a'.map σ)ᵀ * a' = D := by rw [← hDa, Matrix.mul_assoc, haa, Matrix.mul_one]
  have e1 : ((a' * Y * a).map σ)ᵀ * (a' * Y * a) = (a.map σ)ᵀ * ((Y.map σ)ᵀ * D * Y) * a := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← hD2]
    simp only [Matrix.mul_assoc]
  have hS : ∀ M : Matrix (Fin n) (Fin n) R, ((M.map σ)ᵀ).map Φ = ((M.map Φ).map σ')ᵀ := by
    intro M
    ext i k
    simp [Matrix.map_apply, Matrix.transpose_apply, hσ]
  have h1 : (((a' * Y * a).map σ)ᵀ * (a' * Y * a)).map Φ = (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ := by
    have h2 : ((a.map σ)ᵀ * D * a).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by rw [hD]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero Φ) (map_one Φ)] at h2
    have h3 : (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ = Φ t • (1 : Matrix (Fin n) (Fin n) R') := by
      ext i k
      rcases eq_or_ne i k with rfl | h
      · simp
      · simp [Matrix.one_apply, h]
    rw [e1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hS Y, hX, h3, Matrix.mul_smul, Matrix.smul_mul, h2]
  rw [smul_eq_of_map Φ hker h1, smul_smul, ← add_smul]

private theorem conj_part (Φ : R →+* R') {ε : R} (hΦe : Φ ε = 0)
    {a a' Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1) :
    (a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a').map Φ = Y.map Φ := by
  have e : a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a' = (1 - ε) • Y + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    have e1 : a * (a' * Y * a) * a' = Y := by
      calc a * (a' * Y * a) * a' = (a * a') * Y * (a * a') := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [haa, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, haa]
  rw [e]
  ext i k
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, hΦe]

end Core

section Applications
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

private theorem mem_conj_iff (p : ℕ) (w : Plc E) :
    (p : 𝓞 E) ∈ (conjSrc (conjE E) w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  have key : ∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal ↔
      (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    intro u
    show _ ↔ algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simp
  rw [key, key, GlobalTheory.LocInj.under_conjSrc]

private theorem mx_mem (S : Setup A n p) (h : S.G.GAf) :
    S.mx h * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := h.2

private theorem mx_inv (S : Setup A n p) (h : S.G.GAf) : S.mx h * S.mx h⁻¹ = 1 :=
  Units.mul_inv (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

private theorem mx_inv' (S : Setup A n p) (h : S.G.GAf) : S.mx h⁻¹ * S.mx h = 1 :=
  Units.inv_mul (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

end Applications

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJSurj :
    IdemP → MuStar → JSurj := by
  intro hI hM E _ _ _ A n p _ S T μ hμ a ha h
  obtain ⟨e, heQ, heE⟩ := hI p E
  have heeQ : e * e = e := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show e v * e v = e v
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, one_mul]
    · rw [(heQ v).2 hv, zero_mul]
  have hρe : T.ρ e = 0 := (T.ker e).2 fun v hv => (heQ v).2 hv
  have hkerQ : ∀ z, T.ρ z = 0 → (1 - e) * z = 0 := by
    intro z hz
    have hz' := (T.ker z).1 hz
    refine RestrictedProduct.ext _ _ fun v => ?_
    show (1 - e v) * z v = 0
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, sub_self, zero_mul]
    · rw [hz' v hv, mul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : Af E, ε = finiteAdeleMap ℚ E e := ⟨_, rfl⟩
  rw [← hε] at heE
  have heps : ε * ε = ε := by rw [hε, ← map_mul, heeQ]
  have hΦe : T.Φ ε = 0 := by rw [hε, T.Φ_Q, hρe, TensorProduct.zero_tmul]
  have hker : ∀ z, T.Φ z = 0 → (1 - ε) * z = 0 := by
    intro z hz
    have hz' := (T.Φ_ker z).1 hz
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [map_mul, map_sub, map_one, map_zero]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE w).1 hw, sub_self, zero_mul]
    · rw [hz' w hw, mul_zero]
  have hσe : conjFin (conjE E) ε = ε := by
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [pLoc_conjFin]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE _).1 ((mem_conj_iff p w).2 hw), (heE w).1 hw, map_one]
    · rw [(heE _).2 (mt (mem_conj_iff p w).1 hw), (heE w).2 hw, map_zero]
  obtain ⟨c, hc⟩ : ∃ c : (AfP p)ˣ, c = uSimR (AfP p) h := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ := T.surj (c : AfP p)
  obtain ⟨s1, hs1⟩ := T.surj ((c⁻¹ : (AfP p)ˣ) : AfP p)
  obtain ⟨X, hXd⟩ : ∃ X, X = μ (S.mx h) := ⟨_, rfl⟩
  obtain ⟨X', hXd'⟩ : ∃ X', X' = μ (S.mx h⁻¹) := ⟨_, rfl⟩
  obtain ⟨Xs, hXsd⟩ : ∃ Xs, Xs = μ (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop := ⟨_, rfl⟩
  choose y hy using fun i k => T.Φ_surj (X i k)
  choose y' hy' using fun i k => T.Φ_surj (X' i k)
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Af E), Y = Matrix.of y := ⟨_, rfl⟩
  obtain ⟨Y', hYd'⟩ : ∃ Y' : Matrix (Fin n) (Fin n) (Af E), Y' = Matrix.of y' := ⟨_, rfl⟩
  have hY : Y.map T.Φ = X := by
    ext i k
    rw [hYd]
    exact hy i k
  have hY' : Y'.map T.Φ = X' := by
    ext i k
    rw [hYd']
    exact hy' i k
  have hXX : X * X' = 1 := by rw [hXd, hXd', ← map_mul, mx_inv, map_one]
  have hXX' : X' * X = 1 := by rw [hXd, hXd', ← map_mul, mx_inv', map_one]
  have hXXs : X * Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    rw [hXd, hXsd, ← map_mul, mx_mem, ← hc]
    ext i k
    rw [hμ]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
  have hXsX : Xs * X = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    have h1 : Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • X' := by
      calc Xs = (X' * X) * Xs := by rw [hXX', one_mul]
        _ = X' * (X * Xs) := mul_assoc _ _ _
        _ = _ := by rw [hXXs, Matrix.mul_smul, mul_one]
    rw [h1, Matrix.smul_mul, hXX']
  have hMS := hM (AfP p) E A n μ hμ (S.mx h)
  rw [← hXsd, ← hXd] at hMS
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin n) (Fin n) (Af E), D = Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) := ⟨_, rfl⟩
  have hDT : D.map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [hDd, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact T.Φ_E _
  have hΦt : T.Φ (finiteAdeleMap ℚ E s0) = (c : AfP p) ⊗ₜ[ℚ] (1 : E) := by rw [T.Φ_Q, hs0]
  have hX : ((Y.map T.Φ).map (conjT E (AfP p)))ᵀ * D.map T.Φ * Y.map T.Φ =
      T.Φ (finiteAdeleMap ℚ E s0) • D.map T.Φ := by
    rw [hY, hDT, hΦt, ← hMS, mul_assoc, hXsX, Matrix.mul_smul, mul_one]
  have hD : (a.val.map (conjFin (conjE E)))ᵀ * D * a.val = 1 := by rw [hDd]; exact ha.1
  have hA : a.val * (a⁻¹).val = 1 := Units.mul_inv a
  have hA' : (a⁻¹).val * a.val = 1 := Units.inv_mul a
  have hGG := inv_part T.Φ heps hker hA hA' (Y := Y) (Y' := Y') (by rw [hY, hY', hXX])
  have hGG' := inv_part T.Φ heps hker hA hA' (Y := Y') (Y' := Y) (by rw [hY, hY', hXX'])
  have hStar := star_part T.Φ (conjFin (conjE E)) (conjT E (AfP p)) (t := finiteAdeleMap ℚ E s0) T.Φ_conj heps hσe hker hA hA' hD hX
  have hConj := conj_part T.Φ hΦe hA hA' (Y := Y)
  have h01 : (1 - e) * (s0 * s1 - 1) = 0 := hkerQ _ (by rw [map_sub, map_mul, hs0, hs1, map_one, Units.mul_inv, sub_self])
  have hss : ((1 - e) * s0 + e) * ((1 - e) * s1 + e) = 1 := by
    linear_combination h01 + (s0 * s1 - s0 - s1 + 1) * heeQ
  have hss' : ((1 - e) * s1 + e) * ((1 - e) * s0 + e) = 1 := by rw [mul_comm]; exact hss
  have hmem : (((⟨_, _, hGG, hGG'⟩ : GL (Fin n) (Af E)), (⟨_, _, hss, hss'⟩ : AfQˣ)) : GL (Fin n) (Af E) × AfQˣ) ∈ GUf E n := by
    refine UpperTheory.Gal.CertificateRingHomMap.mem_Sim.2 ?_
    refine hStar.trans ?_
    congr 1
    simp only [map_add (f := _), map_mul, map_sub, map_one, ← hε]
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [← hXd, ← hY]
    exact hConj.symm
  · intro w hw
    apply Units.ext
    refine Matrix.ext fun i k => ?_
    show pLoc E w (((1 - ε) • ((a⁻¹).val * Y * a.val) + ε • (1 : Matrix (Fin n) (Fin n) (Af E))) i k) = (1 : Matrix (Fin n) (Fin n) _) i k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, (heE w).1 hw, sub_self, zero_mul,
      zero_add, one_mul]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem ohat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E)
    {x y : AfP p ⊗[ℚ] E} (hx : x ∈ OHat p E) (hy : y ∈ OHat p E) : x * y ∈ OHat p E := by
  obtain ⟨a, rfl⟩ := T.Φ_surj x
  obtain ⟨b, rfl⟩ := T.Φ_surj y
  rw [← map_mul, T.Φ_int]
  intro w hw
  rw [map_mul, map_mul]
  exact mul_le_one' ((T.Φ_int a).1 hx w hw) ((T.Φ_int b).1 hy w hw)

private theorem one_mem_ohat {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E) :
    (1 : AfP p ⊗[ℚ] E) ∈ OHat p E := by
  rw [← map_one T.Φ, T.Φ_int]
  intro w hw
  simp

theorem UpperTheory.Gal.W2.Seed.pKNIff :
    LatCoord → KNIff := by
  intro hL E _ _ _ A n p _ S T g
  obtain ⟨ν, -, hact, hlat⟩ := hL E A n p S T.μ T.mu
  have hM : T.μ (S.mx (T.j g)) = (T.a * mat g * T.a⁻¹).val.map T.Φ := T.j_mx g
  generalize hY : T.a * mat g * T.a⁻¹ = Y at hM ⊢
  have hactM : ∀ v, ν (S.L.actG (T.j g) v) = (Y.val.map T.Φ) *ᵥ ν v := fun v => by rw [hact, hM]
  have hcol : ∀ k i, ((Y.val.map T.Φ) *ᵥ (Pi.single k 1 : Fin n → AfP p ⊗[ℚ] E)) i = T.Φ (Y.val i k) := by
    intro k i
    simp [Matrix.mulVec_single_one]
  have hsingle : ∀ k, ν.symm (Pi.single k 1) ∈ LaHat S.D := by
    intro k
    rw [hlat]
    intro i
    rw [ν.apply_symm_apply, Pi.single_apply]
    split_ifs
    · exact one_mem_ohat T.toAdT
    · exact zero_mem _
  have hΦ1 : ∀ i k, T.Φ ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) i k := by
    intro i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hw1 : ∀ (w : Plc E) i k, pLoc E w ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by
    intro w i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · constructor
    · intro h w hw i k
      have := (hlat _).1 (h _ (hsingle k)) i
      rw [hactM, ν.apply_symm_apply, hcol, T.Φ_int] at this
      exact this w hw
    · intro h v hv
      rw [hlat]
      intro i
      rw [hactM]
      have hv' := (hlat v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
      rw [Matrix.map_apply, T.Φ_int]
      exact fun w hw => h w hw i k
  · intro N hN
    constructor
    · intro h w hw i k
      obtain ⟨u, hu, e⟩ := h _ (hsingle k)
      have e2 := congrFun (congrArg ν e) i
      rw [hactM, ν.apply_symm_apply, hcol, map_add (f := _), map_nsmul, ν.apply_symm_apply] at e2
      have hui := (hlat u).1 hu i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν u i)
      have hxi := (T.Φ_int x).1 (hx ▸ hui) w hw
      have e3 : T.Φ (Y.val i k - (1 : Matrix (Fin n) (Fin n) (Af E)) i k - (N : Af E) * x) = 0 := by
        rw [map_sub, map_sub, map_mul, hΦ1, hx, map_natCast, e2, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
          Matrix.one_apply, Pi.single_apply]
        simp [eq_comm]
      have e4 := (T.Φ_ker _).1 e3 w hw
      rw [map_sub, map_sub, map_mul, hw1, map_natCast, sub_eq_zero, sub_eq_iff_eq_add'] at e4
      have e5 : ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k = (N : w.adicCompletion E) * pLoc E w x := by
        rw [Matrix.sub_apply]
        show pLoc E w (Y.val i k) - _ = _
        rw [e4]
        ring
      rw [e5, map_mul]
      exact mul_le_of_le_one_right' hxi
    · intro h v hv
      have hv' := (hlat v).1 hv
      have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      obtain ⟨Ninv, hNinvdef⟩ : ∃ Ninv : Af E, Ninv = algebraMap E (Af E) ((N : E)⁻¹) := ⟨_, rfl⟩
      have hNinv : (N : Af E) * Ninv = 1 := by
        rw [hNinvdef, ← map_natCast (algebraMap E (Af E)) N, ← map_mul, mul_inv_cancel₀ hN0, map_one]
      obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E),
          ∀ i k, C i k = T.Φ (Ninv * (Y.val - 1) i k) := ⟨Matrix.of fun i k => T.Φ (Ninv * (Y.val - 1) i k), fun _ _ => rfl⟩
      have hC : Y.val.map T.Φ = 1 + ((N : AfP p ⊗[ℚ] E)) • C := by
        ext i k
        rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hΦ1, hCdef,
          ← map_natCast T.Φ N, ← map_mul, ← map_add]
        congr 1
        rw [← mul_assoc, hNinv, one_mul, Matrix.sub_apply]
        ring
      refine ⟨ν.symm (C *ᵥ ν v), ?_, ?_⟩
      · rw [hlat]
        intro i
        rw [ν.apply_symm_apply]
        simp only [Matrix.mulVec, dotProduct]
        refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
        rw [hCdef, T.Φ_int]
        intro w hw
        have h1 := h w hw i k
        have hp' : (N : w.adicCompletion E) * pLoc E w Ninv = 1 := by
          rw [← map_natCast (pLoc E w) N, ← map_mul, hNinv, map_one]
        have h2 : (N : w.adicCompletion E) ≠ 0 := left_ne_zero_of_mul_eq_one hp'
        have h3 : pLoc E w Ninv = (N : w.adicCompletion E)⁻¹ := eq_inv_of_mul_eq_one_right hp'
        have e : pLoc E w ((Y.val - 1) i k) = ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k := by
          rw [Matrix.sub_apply, map_sub, hw1, Matrix.sub_apply]
          rfl
        rw [map_mul, h3, e, map_mul, map_inv₀]
        exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h2))).2 h1
      · apply ν.injective
        rw [hactM, hC, map_add (f := _), map_nsmul, ν.apply_symm_apply, Matrix.add_mulVec, Matrix.one_mulVec,
          Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLocComm :
    LocComm := by
  intro E _ _ _ n w hw x g hg
  have key : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) * comp u g = comp u g * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) := by
    intro u
    by_cases hu : GlobalTheory.Cong.Apart u w
    · rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw hu, one_mul, mul_one]
    · have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
        by_contra h
        exact hu h
      obtain rfl | rfl := GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu'
      · rw [hg, one_mul, mul_one]
      · have hmem : ((mat g).val.map (conjFin (conjE E)))ᵀ * (mat g).val =
            finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E)) := g.2
        have h2 := congrArg (RingHom.mapMatrix (pLoc E w)) hmem
        have e1 : RingHom.mapMatrix (pLoc E w) (((mat g).val.map (conjFin (conjE E)))ᵀ) =
            ((comp (conjSrc (conjE E) w) g).val.map (conjLoc (conjE E) w))ᵀ := by
          refine Matrix.ext fun i k => ?_
          exact pLoc_conjFin (conjE E) _ w
        have e2 : RingHom.mapMatrix (pLoc E w) (mat g).val = 1 := by
          have : (comp w g).val = 1 := by rw [hg]; rfl
          exact this
        have e3 : RingHom.mapMatrix (pLoc E w) (finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E))) =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          ext i k
          by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
        rw [map_mul, e1, e2, mul_one, e3] at h2
        have hM : RingHom.mapMatrix (conjLoc (conjE E) w) (comp (conjSrc (conjE E) w) g).val =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          have := congrArg Matrix.transpose h2
          rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this
          exact this
        have hinj : Function.Injective (RingHom.mapMatrix (conjLoc (conjE E) w) :
            Matrix (Fin n) (Fin n) _ →+* Matrix (Fin n) (Fin n) _) := by
          intro a b hab
          refine Matrix.ext fun i k => ?_
          exact (conjLoc (conjE E) w).injective (congrFun (congrFun hab i) k)
        apply Units.ext
        apply hinj
        rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hM, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.EulerTw.matrix_ext_pLoc E n fun v => ?_)) ?_)
  · have h3 : (comp v (UpperTheory.Gal.CertificateRingHomMap.loc hw x * g)).val = (comp v (g * UpperTheory.Gal.CertificateRingHomMap.loc hw x)).val := by
      rw [map_mul, map_mul, key v]
    exact h3
  · exact mul_comm (sim (UpperTheory.Gal.CertificateRingHomMap.loc hw x)) (sim g)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem conj_H {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have hc : (IsCMField.complexConj E) ((A.c : 𝓞 E) : E) = (A.c : E) := by
    rw [← A.bar_eq, A.c_real]
  ext i j
  simp only [Arith.H, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  · simp

private theorem H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [Arith.H, ← Matrix.diagonal_smul]
  congr 1

private theorem key {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) E) :
    Matrix.diagonal (fun i => (A.dg n i : E)) *
        (((A.H n).map (IsCMField.complexConj E : E →+* E))⁻¹ * y * (A.H n).map (IsCMField.complexConj E : E →+* E)) =
      y * Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [conj_H]
  have hc : (-(A.c : E)) ≠ 0 := neg_ne_zero.mpr A.c_ne
  have hD : Matrix.diagonal (fun i => (A.dg n i : E)) = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hu : IsUnit (A.H n).det := isUnit_iff_ne_zero.mpr (A.det_ne n)
  rw [hD, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem UpperTheory.Gal.W2.Seed.pMuStar :
    MuStar := by
  intro R E _ _ _ _ _ A n μ hμ x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have hk := key A n ((m.map (IsCMField.complexConj E : E →+* E))ᵀ)
    ext i k
    rw [starT_tmul, hermStar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hμ,
      Matrix.transpose_apply, Matrix.map_apply, hμ, conjT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := congrFun (congrFun hk i) k
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  | add x y hx hy =>
    rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), Matrix.mul_add, hx, hy, map_add (f := _),
      Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul]
end

