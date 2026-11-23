module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.TriOfLines
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.Bundle0001

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J

private lemma weight_gap_ne_succ (e : ℕ) (i j : Fin 2) :
    (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≠ (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j + 1 := by
  fin_cases i <;> fin_cases j <;> simp <;> omega

open scoped Pointwise in
open Matrix in
theorem UpperTheory.V.Z.Keep.keeps2 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A)), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → Block η r → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ [Algebra K L] [IsScalarTower K L Ω] (W : G K Ω →* GL (Fin 2) (Qbar l)), (∀ s, (W s).val = corner (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → Z.Win.Keeps W L := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ C₀ k hΦ A _ _ r hO hB h1 K _ _ _ _ _ hK _ _ W hW
  have hflag : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal →
      ∃ A' : ValuationSubring Ω, IsPlaceOver A' w ∧ ∃ κ, Af.FlagAt N ![(e : ℤ), -(e : ℤ)] W A' κ := by
    have tri_of_lines {k H : Type} [Field k] (T : H → Matrix (Fin 2) (Fin 2) k) (a b : H → k) (x y p q : k)
        (hx : x ≠ 0 ∨ y ≠ 0) (hp : p ≠ 0 ∨ q ≠ 0) (hpx : p * x + q * y = 0)
        (h0 : ∀ s, T s 0 0 * x + T s 0 1 * y = a s * x) (h1 : ∀ s, T s 1 0 * x + T s 1 1 * y = a s * y)
        (h2 : ∀ s, p * T s 0 0 + q * T s 1 0 = b s * p) (h3 : ∀ s, p * T s 0 1 + q * T s 1 1 = b s * q) :
        ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
          ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
          ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = b s := by
      obtain ⟨u, v, huv⟩ : ∃ u v : k, u * x + v * y = 1 := by
        rcases hx with h | h
        · exact ⟨x⁻¹, 0, by field_simp; ring⟩
        · exact ⟨0, y⁻¹, by field_simp; ring⟩
      have hd : u * q - v * p ≠ 0 := fun e => by
        have e1 : q = (u * q - v * p) * x := by linear_combination (-q) * huv + v * hpx
        have e2 : p = -(u * q - v * p) * y := by linear_combination (-p) * huv + u * hpx
        rw [e, zero_mul] at e1
        rw [e, neg_zero, zero_mul] at e2
        rcases hp with h | h
        · exact h e2
        · exact h e1
      set d := u * q - v * p with hdd
      let Q0 : Matrix (Fin 2) (Fin 2) k := !![u, v; p, q]
      let Q1 : Matrix (Fin 2) (Fin 2) k := !![x, -v / d; y, u / d]
      have hQ : Q0 * Q1 = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination huv
        · field_simp; ring
        · linear_combination hpx
        · field_simp; rw [hdd]; ring
      let Q : GL (Fin 2) k := ⟨Q0, Q1, hQ, mul_eq_one_comm.1 hQ⟩
      refine ⟨Q, fun s => ?_⟩
      have e : ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Q1 := rfl
      have e' : (Q : Matrix (Fin 2) (Fin 2) k) = Q0 := rfl
      rw [e, e']
      have a0 := h0 s
      have a1 := h1 s
      have a2 := h2 s
      have a3 := h3 s
      refine ⟨?_, ?_, ?_⟩
      · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
        linear_combination x * a2 + y * a3 + b s * hpx
      · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
        linear_combination u * a0 + v * a1 + a s * huv
      · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
        field_simp
        linear_combination (-v) * a2 + u * a3

    have flag_block {k H : Type} [Field k] (R : H → Matrix (Fin 3) (Fin 3) k) (a c : H → k) (g : GL (Fin 3) k)
        (hb : ∀ s, R s 0 1 = 0 ∧ R s 1 0 = 0 ∧ R s 1 2 = 0 ∧ R s 2 1 = 0 ∧ R s 1 1 = 1)
        (ht : ∀ s, ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 1 0 = 0 ∧
          ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 0 = 0 ∧
          ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 1 = 0 ∧
          ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a s ∧
          ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 2 = c s)
        (s0 s2 : H) (h0 : a s0 ≠ 1) (h2 : c s2 ≠ 1) :
        ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
          ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
          ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = c s := by
      obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) k, P = (g : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
      obtain ⟨I, hI⟩ : ∃ I : Matrix (Fin 3) (Fin 3) k, I = ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
      have hPI : P * I = 1 := by rw [hP, hI, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hIP : I * P = 1 := by rw [hP, hI, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [← hP, ← hI] at ht
      have hcol : ∀ s i, (R s * I) i 0 = a s * I i 0 := fun s i => by
        obtain ⟨t1, t2, -, t4, -⟩ := ht s
        have e : R s * I = I * (P * R s * I) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hIP, Matrix.one_mul]
        rw [e, Matrix.mul_apply, Fin.sum_univ_three, t1, t2, t4]
        ring
      have hrow : ∀ s j, (P * R s) 2 j = c s * P 2 j := fun s j => by
        obtain ⟨-, t2, t3, -, t5⟩ := ht s
        have e : P * R s = (P * R s * I) * P := by
          rw [Matrix.mul_assoc _ I P, hIP, Matrix.mul_one]
        rw [e, Matrix.mul_apply, Fin.sum_univ_three, t2, t3, t5]
        ring
      have hz : I 1 0 = 0 := by
        have h := hcol s0 1
        obtain ⟨-, b2, b3, -, b5⟩ := hb s0
        rw [Matrix.mul_apply, Fin.sum_univ_three, b2, b3, b5] at h
        have h' : (a s0 - 1) * I 1 0 = 0 := by linear_combination -h
        exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h0)
      have ht1 : P 2 1 = 0 := by
        have h := hrow s2 1
        obtain ⟨b1, -, -, b4, b5⟩ := hb s2
        rw [Matrix.mul_apply, Fin.sum_univ_three, b1, b4, b5] at h
        have h' : (c s2 - 1) * P 2 1 = 0 := by linear_combination -h
        exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h2)
      have e20 : P 2 0 * I 0 0 + P 2 2 * I 2 0 = 0 := by
        have h := congrFun (congrFun hPI 2) 0
        rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_ne (by decide)] at h
        linear_combination h
      have e00 : P 0 0 * I 0 0 + P 0 2 * I 2 0 = 1 := by
        have h := congrFun (congrFun hPI 0) 0
        rw [Matrix.mul_apply, Fin.sum_univ_three, hz, Matrix.one_apply_eq] at h
        linear_combination h
      have e22 : P 2 0 * I 0 2 + P 2 2 * I 2 2 = 1 := by
        have h := congrFun (congrFun hPI 2) 2
        rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_eq] at h
        linear_combination h
      have hx : I 0 0 ≠ 0 ∨ I 2 0 ≠ 0 := by
        by_contra hc
        push Not at hc
        rw [hc.1, hc.2] at e00
        simp at e00
      have hp : P 2 0 ≠ 0 ∨ P 2 2 ≠ 0 := by
        by_contra hc
        push Not at hc
        rw [hc.1, hc.2] at e22
        simp at e22
      refine tri_of_lines (fun s => corner (R s)) a c (I 0 0) (I 2 0) (P 2 0) (P 2 2) hx hp e20 (fun s => ?_) (fun s => ?_)
        (fun s => ?_) (fun s => ?_)
      · have h := hcol s 0
        rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
        show R s 0 0 * I 0 0 + R s 0 2 * I 2 0 = _
        linear_combination h
      · have h := hcol s 2
        rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
        show R s 2 0 * I 0 0 + R s 2 2 * I 2 0 = _
        linear_combination h
      · have h := hrow s 0
        rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
        show P 2 0 * R s 0 0 + P 2 2 * R s 2 0 = _
        linear_combination h
      · have h := hrow s 2
        rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
        show P 2 0 * R s 0 2 + P 2 2 * R s 2 2 = _
        linear_combination h

    have ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
        (A : ValuationSubring Ω) (hv : A.valuation (l : Ω) < 1) {M : ℕ} (hM : 1 ≤ M) (d : ℤ) (hd : d ≠ 0)
        (χ : G F Ω →* (Qbar l)ˣ) (hχ : Af.KillsMu M χ) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
        (hI : ∀ s : ↥(Dec (F := F) A), (s : G F Ω) ∈ Ine (F := F) A → κ s = cycBar F Ω l s ^ d * χ s) :
        ∃ s, κ s ≠ 1 := by
      have hfin : Finite χ.range := (UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ hχ).to_subtype
      have hN : ∀ s, χ s ^ Nat.card χ.range = 1 := fun s =>
        congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, s, rfl⟩ : χ.range)))
      have hN0 : Nat.card χ.range ≠ 0 := Nat.card_pos.ne'
      obtain ⟨g, hg, hne⟩ := UpperTheory.V.Ws.Pt.cycIne F Ω l A hv (d * Nat.card χ.range)
        (mul_ne_zero hd (by exact_mod_cast hN0))
      refine ⟨⟨g, Ine_le_Dec A hg⟩, fun e => hne ?_⟩
      have h1 := hI ⟨g, Ine_le_Dec A hg⟩ hg
      rw [e] at h1
      have h2 : cycBar F Ω l g ^ d = (χ g)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      rw [_root_.zpow_mul, h2, zpow_natCast, inv_pow, hN, inv_one]

    intro w hw
    have hker : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => by
      rw [hK, ← range_galEmb]
      exact ⟨s, rfl⟩
    let j : G K Ω →* η.ker := (galEmb ℚ K Ω).codRestrict _ hker
    let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart η (UnitaryThreeInertia.push A.val r) hO.red.mult).comp j
    have hρ : ∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat := fun s => rfl
    have hord3 : ∃ P : ValuationSubring Ω, IsPlaceOver P w ∧
        ∃ κ, Af.FlagAt N ![(e : ℤ), 0, -(e : ℤ)] ρ P κ := by
      have diag_mul_of_tri {k : Type} [CommRing k] (A B : Matrix (Fin 3) (Fin 3) k)
          (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin 3) :
          (A * B) i i = A i i * B i i := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
        rcases lt_or_gt_of_ne hj with h | h
        · rw [hA (show id j < id i from h), zero_mul]
        · rw [hB (show id i < id j from h), mul_zero]

      have chars_of_tri {H k : Type} [Group H] [Field k] (T : H →* GL (Fin 3) k)
          (tri : ∀ s, (T s).val.BlockTriangular id) :
          ∃ κ : Fin 3 → H →* kˣ, ∀ s i, ((κ i s : kˣ) : k) = (T s).val i i := by
        let d : Fin 3 → H →* k := fun i =>
          { toFun := fun s => (T s).val i i
            map_one' := by simp
            map_mul' := fun a b => by
              rw [map_mul, Units.val_mul]
              exact diag_mul_of_tri _ _ (tri a) (tri b) i }
        exact ⟨fun i => (d i).toHomUnits, fun s i => by simp [d]⟩

      have theta_upper {k : Type} [Field k] (b : GL (Fin 3) k) (hb : b.val.BlockTriangular id) :
          (theta b).val.BlockTriangular id ∧ ∀ i, (theta b).val i i = (b.val i.rev i.rev)⁻¹ := by
        have hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id := by
          have : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩
          rw [Matrix.coe_units_inv]
          exact Matrix.blockTriangular_inv_of_blockTriangular hb
        have hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹ := fun i => by
          have h1 := congrFun (congrFun (Units.mul_inv b) i) i
          rw [diag_mul_of_tri _ _ hb hc, Matrix.one_apply_eq] at h1
          exact eq_inv_of_mul_eq_one_right h1
        have he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev := fun i j => by
          rw [theta_val]
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · rw [he]
          exact hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)
        · rw [he, hd]

      have weight_rev_eq_neg (i : Fin 3) : wt1 i.rev = - wt1 i := by
        fin_cases i <;> simp [wt1, Fin.rev]

      have left_conj_pos {k : Type} [CommRing k] (x y : GG (m := 3) (R := k)) (h1 : x.right = 1) (h2 : y.right = 1) :
          (x * y * x⁻¹).left = x.left * y.left * x.left⁻¹ := by
        simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2]

      have left_conj_neg {k : Type} [CommRing k] (x y : GG (m := 3) (R := k)) (h1 : x.right = -1) (h2 : y.right = 1) :
          (x * y * x⁻¹).left = x.left * theta y.left * x.left⁻¹ := by
        simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, theta_theta]

      have conj_left {D A : Type} [Group D] [CommRing A] (h : GL (Fin 3) A) (r : D →* GG (m := 3) (R := A)) (s : D)
          (hs : (r s).right = 1) : (conjBy h⁻¹ r s).left = h⁻¹ * (r s).left * h := by
        simp [conjBy, hs]

      have flag_core {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] (R : Γ →* GG (m := 3) (R := k)) (ι : Δ →* Γ)
          (ρ : Δ →* GL (Fin 3) k) (hρ : ∀ s, ρ s = (R (ι s)).left) (hK : ∀ s, (R (ι s)).right = 1)
          (H : Subgroup Δ) (I : Set Δ) (t : Γ) (b : GL (Fin 3) k) (c : Δ →* kˣ)
          (tri : ∀ s ∈ H, (b * (R (t⁻¹ * ι s * t)).left * b⁻¹ : GL (Fin 3) k).val.BlockTriangular id)
          (ine : ∀ s ∈ H, s ∈ I → ∀ i, (b * (R (t⁻¹ * ι s * t)).left * b⁻¹ : GL (Fin 3) k).val i i = ((c s ^ wt1 i : kˣ) : k)) :
          ∃ κ : Fin 3 → ↥H →* kˣ, Af.IsFlagOn ρ H κ ∧ ∀ i (s : ↥H), (s : Δ) ∈ I → κ i s = c s ^ wt1 i := by
        have hY : ∀ s, (R (t⁻¹ * ι s * t)).right = 1 := fun s => by
          have e : ∀ x, (R x).right = (GG.nu (R x)) := fun _ => rfl
          rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ← e (ι s), hK]
          simp
        have hc : ∀ s, R (ι s) = R t * R (t⁻¹ * ι s * t) * (R t)⁻¹ := fun s => by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          group

        suffices hs : ∃ P : GL (Fin 3) k, ∃ f : GL (Fin 3) k →* GL (Fin 3) k,
            (∀ s, P * ρ s * P⁻¹ = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)) ∧
            (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → (f x).val.BlockTriangular id) ∧
            (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → ∀ y : kˣ, (∀ i, x.val i i = ((y ^ wt1 i : kˣ) : k)) →
              ∀ i, (f x).val i i = ((y ^ wt1 i : kˣ) : k)) by
          obtain ⟨P, f, h1, h2, h3⟩ := hs
          let T : ↥H →* GL (Fin 3) k := (MulAut.conj P).toMonoidHom.comp (ρ.comp H.subtype)
          have hT : ∀ s : ↥H, T s = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹) := fun s => h1 s
          obtain ⟨κ, hκ⟩ := chars_of_tri T fun s => by
            rw [hT]
            exact h2 _ (tri s s.2)
          refine ⟨κ, ⟨P, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => Units.ext ?_⟩
          · have : (T s).val.BlockTriangular id := by
              rw [hT]
              exact h2 _ (tri s s.2)
            exact this hij
          · exact (hκ s i).symm
          · rw [hκ, hT]
            exact h3 _ (tri s s.2) _ (ine s s.2 hs) i
        rcases Int.units_eq_one_or (R t).right with ht | ht
        · refine ⟨b * (R t).left⁻¹, MonoidHom.id _, fun s => ?_, fun x h => h, fun x _ y h => h⟩
          have e1 : ρ s = (R t).left * (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹ :=
            (hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_pos _ _ ht (hY s)))
          rw [e1, MonoidHom.id_apply]
          group
        · refine ⟨theta b * (R t).left⁻¹, thetaAut 3 k, fun s => ?_, fun x h => (theta_upper x h).1, fun x hx y h i => ?_⟩
          · have e1 : ρ s = (R t).left * theta (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹ :=
              (hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_neg _ _ ht (hY s)))
            have e2 : ∀ x y : GL (Fin 3) k, theta (x * y * x⁻¹) = theta x * theta y * (theta x)⁻¹ := fun x y => by
              have e : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x := fun _ => rfl
              simp only [e, map_mul, map_inv]
            show _ = theta (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)
            rw [e1, e2]
            group
          · show (theta x).val i i = _
            rw [(theta_upper x hx).2, h, weight_rev_eq_neg]
            simp

      have cls_of_fix {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω] (N : ℕ) [NeZero N]
          (s : G K Ω) (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1 := by
        have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
        have : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
        obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
        have h1 := Chr.cls_spec N (galEmb ℚ K Ω s) ζ hζ.pow_eq_one
        rw [galEmb_apply, h ζ hζ.pow_eq_one] at h1
        nth_rewrite 1 [← pow_one ζ] at h1
        have h2 : (1 : ℕ) ≡ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val [MOD N] := by
          obtain ⟨z, rfl⟩ := hζ.isUnit (NeZero.ne N)
          have hz : IsPrimitiveRoot z N := IsPrimitiveRoot.coe_units_iff.1 hζ
          have h0 : z ^ 1 = z ^ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val := Units.ext (by simpa using h1)
          have h4 := (pow_eq_pow_iff_modEq).1 h0
          rwa [← hz.eq_orderOf] at h4
        apply Units.ext
        have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
        rw [ZMod.natCast_zmod_val] at h3
        simpa using h3.symm

      obtain ⟨P, hP⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
      refine ⟨P, hP, ?_⟩
      have hPl : P.valuation (l : Ω) < 1 := by
        have := hP ((l : ℕ) : 𝓞 K)
        simp only [map_natCast] at this
        exact this.2 hw
      obtain ⟨v, u, -, hPv⟩ := (k.pl_all P hPl).exists
      obtain ⟨γ, -, hpl⟩ := k.pl_conj v
      have hPt : P = (u * γ) • B := by rw [hPv, hpl, mul_smul]
      generalize u * γ = t at hPt
      have hA : ∀ x, t.toRingEquiv x ∈ P ↔ x ∈ B := fun x => by
        rw [hPt]
        exact ValuationSubring.smul_mem_pointwise_smul_iff (g := t)
      have hL : IsLift (RingEquiv.refl ℚ) t.toRingEquiv := fun x => t.commutes x
      have hcg : ∀ g : G ℚ Ω, conjGal hL g = t⁻¹ * g * t := fun _ => rfl
      have hmem : ∀ s : G K Ω, η (galEmb ℚ K Ω s) = 1 := fun s => by
        have : galEmb ℚ K Ω s ∈ η.ker := hK ▸ galEmb_mem ℚ K Ω s
        exact this
      have hright : ∀ g, (UnitaryThreeInertia.push A.val r g).right = η g := hO.red.mult
      have hη : ∀ s, η (t⁻¹ * galEmb ℚ K Ω s * t) = 1 := fun s => by
        rw [map_mul, map_mul, map_inv, hmem, mul_one, inv_mul_cancel]
      have hdec : ∀ s ∈ Dec (F := K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Dec (F := ℚ) B := fun s hs =>
        hcg _ ▸ conjGal_mem_Dec hL hA (show galEmb ℚ K Ω s ∈ Dec (F := ℚ) P from hs)
      have hine : ∀ s ∈ Ine (F := K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Ine (F := ℚ) B := fun s hs =>
        hcg _ ▸ conjGal_mem_Ine hL hA (show galEmb ℚ K Ω s ∈ Ine (F := ℚ) P from hs)
      obtain ⟨h, -, tri, ine⟩ := hO.ord
      let f : A →+* Qbar l := (A.val : A →+* PadicAlgCl l)
      let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map f h
      let a : (c.O)ˣ →* (Qbar l)ˣ := Units.map (algebraMap c.O (Qbar l)).toMonoidHom
      let d : G K Ω →* (Qbar l)ˣ := a.comp ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))
      let cc : G K Ω →* (Qbar l)ˣ := a.comp ((Chr.Psi l e (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ K Ω))
      have hent : ∀ s (hs : s ∈ Dec (F := K) P) i j,
          (h'⁻¹ * (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h'⁻¹⁻¹ : GL (Fin 3) (Qbar l)).val i j =
            f ((conjBy h⁻¹ (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩).mat i j) := fun s hs i j => by
        have e1 : (r (t⁻¹ * galEmb ℚ K Ω s * t)).right = 1 := (hO.red.mult _).trans (hη s)
        have e2 := conj_left h (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩ e1
        have e3 : (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left =
          Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left := rfl
        rw [GG.mat, e2, e3, inv_inv]
        have e4 : h'⁻¹ * Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h' =
          Matrix.GeneralLinearGroup.map f (h⁻¹ * (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h) := by
          simp only [h', map_mul, map_inv]
        rw [e4]
        rfl
      obtain ⟨κ, hf, hκ⟩ := flag_core (UnitaryThreeInertia.push A.val r) (galEmb ℚ K Ω) ρ (fun s => Units.ext (hρ s))
        (fun s => (hright _).trans (hmem s)) (Dec (F := K) P) (Ine (F := K) P : Set (G K Ω)) t h'⁻¹ cc
        (fun s hs i j hij => by
          rw [hent s hs]
          have hij' : (j : ℕ) < i := hij
          rw [tri ⟨_, hdec s hs⟩ (hη s) i j (by simp only [wt, wt1]; omega), map_zero])
        (fun s hs hi i => by
          rw [hent s hs]
          have := ine ⟨_, hdec s hs⟩ (Subgroup.mem_subgroupOf.2 (hine s hi)) (hη s) i
          rw [this]
          have hx : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s) := by
            rw [map_mul, map_mul, map_inv, mul_comm _ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) t), mul_inv_cancel_left]
          have e1 : cc s ^ wt1 i = a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) ^ wt1 i) := by
            rw [hx, map_zpow]
            rfl
          rw [e1]
          exact A.val.commutes _)
      have hm : ∀ i : Fin 3, ![(e : ℤ), 0, -(e : ℤ)] i = (e : ℤ) * wt1 i := fun i => by
        fin_cases i <;> simp [wt1]
      have hcc : ∀ s, cc s = cycBar K Ω l s ^ (e : ℤ) * d s := fun s => by
        have e1 : a (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) = cycBar K Ω l s := Units.ext rfl
        show a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s)) = _
        rw [Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, e1]
        rfl
      refine ⟨κ, fun i => d ^ wt1 i, fun i s hs => ?_, hf, fun i s hs => ?_⟩
      · have hd : d s = 1 := by
          simp [d, Chr.dirG, cls_of_fix N s hs]
        rw [MonoidHom.zpow_apply, hd, _root_.one_zpow]
      · rw [hκ i s hs, hcc, mul_zpow, ← _root_.zpow_mul, hm, MonoidHom.zpow_apply]
    obtain ⟨A', hA, κ, χ, hχ, ⟨g, hg⟩, hI⟩ := hord3
    have hv : A'.valuation (l : Ω) < 1 := by
      simpa using (hA _).2 hw
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have he : (e : ℤ) ≠ 0 := by
      have := hL.e_pos
      omega
    obtain ⟨s0, h0⟩ := ne_one A' hv hN (e : ℤ) he (χ 0) (hχ 0) (κ 0) (hI 0)
    obtain ⟨s2, h2⟩ := ne_one A' hv hN (-(e : ℤ)) (neg_ne_zero.2 he) (χ 2) (hχ 2) (κ 2) (hI 2)
    have hent : ∀ (s : G K Ω) (a b : Fin 3), Odd (wt a b) → (ρ s).val a b = 0 := fun s a b h => by
      rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, hB _ (hker s) a b h]
      exact map_zero _
    have hmid : ∀ s : G K Ω, (ρ s).val 1 1 = 1 := fun s => by
      rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, h1 _ (hker s)]
      exact map_one _
    obtain ⟨Q, hQ⟩ := flag_block (fun s : ↥(Dec (F := K) A') => (ρ s.1).val)
      (fun s => ((κ 0 s : (Qbar l)ˣ) : Qbar l)) (fun s => ((κ 2 s : (Qbar l)ˣ) : Qbar l)) g
      (fun s => ⟨hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hmid _⟩)
      (fun s => by
        obtain ⟨t1, t2⟩ := hg s
        exact ⟨t1 1 0 (by decide), t1 2 0 (by decide), t1 2 1 (by decide), t2 0, t2 2⟩)
      s0 s2 (fun e => h0 (Units.ext e)) (fun e => h2 (Units.ext e))
    refine ⟨A', hA, ![κ 0, κ 2], ![χ 0, χ 2], fun i => ?_, ⟨Q, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => ?_⟩
    · fin_cases i
      · exact hχ 0
      · exact hχ 2
    · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
        rw [Units.val_mul, Units.val_mul, hW, ← hρ]
      have hij' : i = 1 ∧ j = 0 := by
        revert hij; fin_cases i <;> fin_cases j <;> simp
      obtain ⟨rfl, rfl⟩ := hij'
      show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 0 = 0
      rw [e1]
      exact (hQ s).1
    · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
        rw [Units.val_mul, Units.val_mul, hW, ← hρ]
      fin_cases i
      · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 0 0 = _
        rw [e1]
        exact (hQ s).2.1
      · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 1 = _
        rw [e1]
        exact (hQ s).2.2
    · fin_cases i
      · exact hI 0 s hs
      · exact hI 2 s hs
  exact UpperTheory.V.Z.Keep.keepsGap K L Ω l 2 N ![(e : ℤ), -(e : ℤ)] W
    NeZero.one_le hflag (weight_gap_ne_succ e)
