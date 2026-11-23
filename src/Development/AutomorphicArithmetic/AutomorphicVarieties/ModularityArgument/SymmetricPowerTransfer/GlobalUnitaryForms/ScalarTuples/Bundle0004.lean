module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ChiVal
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.CharacterValues

private theorem hs_mul_sq {K : Type} [Field K] (D x s : K) (h0 : s ≠ 0) : hs D (x * s ^ 2) = hs D x := by
  unfold hs
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a / s, b / s, ?_⟩
    field_simp
    linear_combination h
  · rintro ⟨a, b, h⟩
    exact ⟨a * s, b * s, by rw [← h]; ring⟩

private theorem hs_sq {K : Type} [Field K] (D x : K) : hs D x ^ 2 = 1 := by
  unfold hs
  split_ifs <;> norm_num

private theorem hs_of_sq {K : Type} [Field K] [CharZero K] (D x : K) (h0 : D ≠ 0) (h : IsSquare D) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

private theorem card_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : O} (hp : Irreducible p)
    (u : Oˣ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {(u : O) * p ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have e : Ideal.span {(u : O) * p ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, hp.maximalIdeal_eq]
  rw [e]
  exact cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal O) (IsDiscreteValuationRing.not_a_field O)

private theorem main {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (inj : Function.Injective (algebraMap O K)) (Δ : K) (χ : Kˣ →* ℂˣ) (hχ : IsChi O Δ χ)
    (hu : ∀ u : Oˣ, hs Δ (algebraMap O K u) = 1) (x : Kˣ) (x₀ : O) (hx : algebraMap O K x₀ = x) :
    (χ x : ℂ) = hs Δ (x : K) / (Nat.card (O ⧸ Ideal.span {x₀}) : ℂ) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hx, map_zero])
  have hp0 : algebraMap O K p ≠ 0 := fun e => hp.ne_zero (inj (e.trans (map_zero _).symm))
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hp
  rw [card_pow hp]
  have hup : Irreducible ((u : O) * p) := (irreducible_units_mul u).2 hp
  set U : Kˣ := Units.map (algebraMap O K : O →* K) u with hU
  set P : Kˣ := Units.mk0 _ hp0 with hP
  have hxe : x = U * P ^ n := by
    ext
    rw [← hx]
    simp [hU, hP]
  have c1 : (χ P : ℂ) = hs Δ (P : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ) := hχ.2 p P hp rfl
  have c2 : (χ (U * P) : ℂ) = hs Δ ((U * P : Kˣ) : K) / (Nat.card (IsLocalRing.ResidueField O) : ℂ) :=
    hχ.2 (u * p) (U * P) hup (by simp [hU, hP])
  have c3 : χ U = 1 := hχ.1 u
  have c4 : hs Δ (U : K) = 1 := hu u
  have c5 : ∀ k : ℕ, (χ (P ^ (2 * k)) : ℂ) = 1 / (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * k) := fun k => by
    rw [map_pow, Units.val_pow_eq_pow_val, c1, div_pow, pow_mul (hs _ _), hs_sq, one_pow]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : ((U * P ^ (2 * k) : Kˣ) : K) = U * ((P : K) ^ k) ^ 2 := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val]; ring
    rw [hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), c4, map_mul, c3, one_mul, c5, Nat.cast_pow]
  · have e : ((U * P ^ (2 * k + 1) : Kˣ) : K) = ((U * P : Kˣ) : K) * ((P : K) ^ k) ^ 2 := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]; ring
    have e' : U * P ^ (2 * k + 1) = U * P * P ^ (2 * k) := by rw [pow_succ', mul_assoc]
    rw [hxe, e, hs_mul_sq _ _ _ (pow_ne_zero _ P.ne_zero), e', map_mul, Units.val_mul, c2, c5, Nat.cast_pow,
      div_mul_div_comm, mul_one, pow_succ']

end UpperTheory.V.Z.Sym.Glob.CharacterValues

open UpperTheory.V.Z.Sym.Glob.CharacterValues in
theorem UpperTheory.V.Z.Sym.Glob.chiVal :
    UpperTheory.V.Z.Sym.Glob.ChiVal := by
  intro F _ _ Δ D hD v x x₀ hx
  refine main (fun a b h => Subtype.ext h) _ _ (hD.chi v) (fun u => ?_) x x₀ hx
  by_cases hv : v ∈ D.Sg
  · haveI := hD.real
    haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
    have hΔ : Δ ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      have := hD.neg (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w))
      rintro rfl
      simp at this
    exact hs_of_sq _ _ ((map_ne_zero _).2 hΔ) (hD.split v hv)
  · have h := hD.off v hv
    exact (hsLaw _ _ _ h).2.1 _ _ h.even ⟨u, 1, one_ne_zero, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GqS
section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.gqS :
    UpperTheory.V.Z.Sym.Glob.GqS := by
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj
  haveI := hD.real
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ) :=
    fun g v hg => hasTr_map (cv v) (hι g v) hg
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ))
      (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_
    · intro v u hu x
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        have hu' : u ∈ (D.S v).J2 := by simpa [Dat.J2v, hv] using hu
        simp only [Dat.fSv, if_pos hv]
        rw [(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]
      · have hu' : u ∈ KD ((cv v) Δ) (Ov v) := by simpa [Dat.J2v, hv] using hu
        have hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v) := by
          rw [(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu',
            (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]
        simp only [Dat.fSv, if_neg hv, one]
        by_cases hx : x ∈ KD ((cv v) Δ) (Ov v)
        · rw [if_pos hx, if_pos (hiff.2 hx)]
        · rw [if_neg hx, if_neg (fun h => hx (hiff.1 h))]
    · intro v jv hjv
      have hgv : HasTr ((ι γ).1 v) (cv v τ) := htr γ v hγ
      have hrv := cv_reg hreg v
      obtain ⟨z, hz⟩ := zEx hrv
      refine ⟨emb_comm hjv, ?_⟩
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        obtain ⟨hF, -, hO, -, -⟩ := hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz
        have e1 : D.fSv t v = (D.S v).fS (t v) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨hF, fun _ => ?_, fun h => absurd hv h⟩
        rw [hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]
      · have hL := hD.off v hv
        have e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v)) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = KD ((cv v) Δ) (Ov v) := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu =>
            ⟨if_pos hK, fun y hy => ?_⟩⟩⟩
        have hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
          by_contra hn
          exact hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))
        exact (oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    apply gqOn_zero
    intro y
    obtain ⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by
      simpa [Dat.admitted] using hA
    have heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v =
        ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v := rfl
    have hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ) := by
      rw [heq]
      exact hasTr_conj (htr γ v hγ) _
    have hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0 := by
      simp only [Dat.fSv, if_pos hv]
      by_contra hne
      exact hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)
    exact fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsScal
section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_eq {K : Type} [Field K] {Δ τ τ' : K} (hr : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} {j} (hγ : HasTr γ τ) (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (y : DX Δ)
    (h : (mt (y⁻¹ * j z * y)).trace ^ 2 = algebraMap K _ (2 + τ') * (mt (y⁻¹ * j z * y)).det) : τ' = τ := by
  have e : mt (y⁻¹ * j z * y) = mt y⁻¹ * mt (j z) * mt y := rfl
  have e' : mt y * mt y⁻¹ = 1 := by
    change mt (y * y⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e1 : mt (j z) = 1 + mt γ := by rw [hj, hz]; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h1 := hγ.1
  have h2 := hγ.2
  rw [Matrix.det_fin_two] at h1
  rw [Matrix.trace_fin_two] at h2
  have t1 : (mt (j z)).trace = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.trace_fin_two, map_add (f := _), map_ofNat, ← h2]; simp; ring
  have t2 : (mt (j z)).det = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.det_fin_two, map_add (f := _), map_ofNat, ← h2]; simp; linear_combination h1
  rw [e, Matrix.trace_mul_cycle, e', one_mul, Matrix.det_mul, mul_comm _ (mt y).det, Matrix.det_mul, ← mul_assoc (mt y).det,
    ← Matrix.det_mul, e', Matrix.det_one, one_mul, t1, t2, ← map_pow, ← map_mul] at h
  have h3 := (algebraMap K (Lsq K Δ)).injective h
  have h4 : 2 + τ ≠ 0 := fun e => hr (by linear_combination (τ - 2) * e)
  exact mul_right_cancel₀ h4 (by linear_combination -h3)

theorem UpperTheory.V.Z.Sym.Glob.gqK :
    UpperTheory.V.Z.Sym.Glob.GqK := by
  classical
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj z hz
  haveI := hD.real
  have hr := cm_ne hτ
  have htr : ∀ v, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map _ (hι γ v) hγ
  have f1 : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun g => if_pos hv
  have f2 : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun g => if_neg hv
  have J1 : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have J2 : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  choose zv hzv using fun v => zEx (cv_reg hr v)
  have ez : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (ι (j z)).1 v = jv (zv v) := fun v jv hjv =>
    dx_ext ((hι (j z) v).trans (emb_map _ (hι γ v) hj hjv z _ (by
      rw [hzv, hz]; ext <;> simp [emap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])).symm)
  have k1 : ∀ v ∉ D.Sg, ∀ k ∈ KD _ (Ov v), fZD (Ov v) (D.χ v) k = 1 := fun v hv k hk => by
    have := (Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).2 1 1 k (by simp [IsScal, mt]) hk
    simpa using this
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj (j z) (D.fKv t) (fun v => ?_) _ _ fun v jv hjv => ?_
    · by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        intro u hu x
        rw [(((hD.sig v hv).K_inv _ (ht v hv)).1 u hu _).2, (((hD.sig v hv).K_inv _ (ht v hv)).1 _ (inv_mem hu) _).1]
      · rw [f2 v hv, J2 v hv]
        exact fZD_conj _ (hD.off v hv) _ (hD.chi v).1
    · rw [ez v jv hjv]
      refine ⟨fun s => by rw [← map_mul, ← map_mul, mul_comm], ?_⟩
      by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        obtain ⟨-, h1, -, h3, -⟩ := (hD.sig v hv).D_orb _ (ht v hv) _ _ _ (cv_reg hr v) (htr v) hjv _ (hzv v)
        exact ⟨h1, fun _ => by rw [h3, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one], fun h => absurd hv h⟩
      · rw [f2 v hv, J2 v hv]
        refine ⟨(Loc.finD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv).2.1 _ (hzv v) _, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv _ (hD.chi v).1 _ (hzv v)).2, fun h1 h2 => ?_⟩⟩
        obtain ⟨h3, h4⟩ := (Loc.oneD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv h1 h2).2.2 _ (hzv v)
        refine ⟨k1 v hv _ h3, fun y hy => h4 y ?_⟩
        by_contra h
        exact hy ((Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).1 _ h)
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    refine gqOn_zero _ _ _ _ fun y => ?_
    obtain ⟨v, hv⟩ := not_forall.1 hA
    obtain ⟨hv, hI⟩ := Classical.not_imp.1 hv
    refine fin_mulSupp (D.fKv t) D.Sg (fun v hv k hk => by rw [f2 v hv]; exact k1 v hv k hk) _ (v := v) ?_
    rw [f1 v hv]
    by_contra h
    haveI : CharZero (Kv v) := algebraRat.charZero _
    obtain ⟨jv, hjv⟩ := (embAlg (Kv v) _ _ ((map_ne_zero _).2 hD.ne0) (cv_reg hr v) _ (htr v)).1
    have h' : (D.S v).fK (t v) ((y.out.1 v)⁻¹ * (ι (j z)).1 v * y.out.1 v) ≠ 0 := h
    rw [ez v jv hjv] at h'
    obtain ⟨τ', h1, h2⟩ := (hD.sig v hv).K_supp _ (ht v hv) _ h'
    exact hI (tau_eq (cv_reg hr v) (htr v) hjv (hzv v) _ h2 ▸ h1)
end

