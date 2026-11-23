module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LowerTriangularConjAntidiag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj {K : Type} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Mᵀ * Jmat (R := K) n) i j = M j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat]
  simp [Fin.rev_eq_iff]
  simp [eq_comm (a := j), Fin.rev_eq_iff]

private theorem ord3 {K : Type} [CommRing K] (α β γ p₀ q₀ p₁ q₁ p₂ q₂ : K) :
    (!![p₀, 0, 0; (p₀ - 1) * α, 1, 0; (p₀ - q₀) * γ - (1 - q₀) * (α * β), (1 - q₀) * β, q₀] -
        p₀ • (1 : Matrix (Fin 3) (Fin 3) K)) *
      ((!![p₁, 0, 0; (p₁ - 1) * α, 1, 0; (p₁ - q₁) * γ - (1 - q₁) * (α * β), (1 - q₁) * β, q₁] -
        (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (!![p₂, 0, 0; (p₂ - 1) * α, 1, 0; (p₂ - q₂) * γ - (1 - q₂) * (α * β), (1 - q₂) * β, q₂] -
        q₂ • (1 : Matrix (Fin 3) (Fin 3) K))) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> ring

private theorem low_pol {K : Type} [CommRing K] (p q y z a : K) :
    !![q, 0, 0; z, 1, 0; a, y, p] =
      Jmat (R := K) 3 * (!![p, 0, 0; y, 1, 0; a, z, q])ᵀ * Jmat (R := K) 3 := by
  ext i j
  rw [jconj]
  fin_cases i <;> fin_cases j <;> rfl

private theorem low_mul {K : Type} [CommRing K] (p q y z a p' q' y' z' a' : K) :
    !![p * p', 0, 0; y * p' + y', 1, 0; a * p' + z * y' + q * a', z + q * z', q * q'] =
      !![p, 0, 0; y, 1, 0; a, z, q] * !![p', 0, 0; y', 1, 0; a', z', q'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem low_diag {K : Type} [CommRing K] (p q p' q' y a : K) (i j : Fin 3) (h : i ≠ j) :
    (!![p, 0, 0; y, 1, 0; a, y, q] - !![p', 0, 0; y, 1, 0; a, y, q'] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_up {K : Type} [CommRing K] (p q y z a : K) (i j : Fin 3) (h : i < j) :
    (!![p, 0, 0; y, 1, 0; a, z, q] : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

theorem UpperTheory.lowerTriangular_conj_antidiag :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (y a : F.G0 → Q), F.Low Q y a → ∃ ρ : NRep F 3 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧ (∀ g, ρ.r g 1 0 = y g) ∧ ∀ g, ρ.r g 2 0 = a g := by
  intro l _ k _ _ F C₀ hF Q _ _ y a h
  obtain ⟨s1, s2, s3, s4, -⟩ := UpperTheory.V.Fr.star hF
  have y1 : y 1 = 0 := by
    have := h.muly 1 1
    simpa using this
  have st1 : F.star 1 = 1 := by simp [Frame.star]
  have a1 : a 1 = 0 := by
    have := h.mula 1 1
    simpa [y1] using this
  let p : F.G0 → Q := fun g => algebraMap k Q (F.Ψ g : k)
  let q : F.G0 → Q := fun g => algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k)
  have pm : ∀ g g', p (g * g') = p g * p g' := fun g g' => by simp [p]
  have qm : ∀ g g', q (g * g') = q g * q g' := fun g g' => by simp [q, mul_comm]
  have ps : ∀ g, p (F.star g) = q g := fun g => by simp only [p, q, s3]
  have qs : ∀ g, q (F.star g) = p g := fun g => by simp only [p, q, s3, inv_inv]
  have ym : ∀ g g', y (g * g') = y g * p g' + y g' := fun g g' => by
    rw [h.muly, Algebra.smul_def, mul_comm]
  have am : ∀ g g', a (g * g') = a g * p g' + y (F.star g) * y g' + q g * a g' := fun g g' => by
    rw [h.mula, Algebra.smul_def, Algebra.smul_def, mul_comm _ (a g)]
  have zm : ∀ g g', y (F.star (g * g')) = y (F.star g) + q g * y (F.star g') := fun g g' => by
    rw [s2, ym, ps]; ring
  let r : F.G0 →* Matrix (Fin 3) (Fin 3) Q :=
    { toFun := fun g => !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [p, q, y1, a1, st1]
      map_mul' := fun g g' => by
        rw [zm, pm, qm, ym, am, low_mul] }
  have hr : ∀ g, r g = !![p g, 0, 0; y g, 1, 0; a g, y (F.star g), q g] := fun _ => rfl
  have w0 : w 3 0 = 1 := rfl
  have w1 : w 3 1 = 0 := rfl
  have w2 : w 3 2 = -1 := rfl
  let ψ : ∀ v, Fin 3 → F.Gv v →* Qˣ := fun v i =>
    (Units.map (algebraMap k Q).toMonoidHom).comp ((zpowGroupHom (w 3 i)).comp (F.Ψ.comp (F.loc v)))
  have hψ : ∀ v i g, (ψ v i g : Q) = algebraMap k Q ((F.Ψ (F.loc v g) ^ w 3 i : kˣ) : k) := fun _ _ _ => rfl
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    have hc : Continuous fun x : F.G0 => (g : F.Γ)⁻¹ * (x : F.Γ) := by fun_prop
    have : ∀ᶠ x : F.G0 in nhds g, (g : F.Γ)⁻¹ * (x : F.Γ) ∈ (F.Ψ.ker : Set F.Γ) :=
      (hF.Ψ_open.preimage hc).mem_nhds (by simp)
    refine this.mono fun x hx => ?_
    have hx' : F.Ψ ((g : F.Γ)⁻¹ * (x : F.Γ)) = 1 := hx
    rw [map_mul, map_inv, inv_mul_eq_one] at hx'
    exact hx'.symm
  have lp : IsLocallyConstant p := hΨ.comp fun u : kˣ => algebraMap k Q (u : k)
  have lq : IsLocallyConstant q := hΨ.comp fun u : kˣ => algebraMap k Q ((u⁻¹ : kˣ) : k)
  have lz : IsLocallyConstant fun g => y (F.star g) := h.lcy.comp_continuous s4
  refine ⟨⟨r, ψ, fun g => ?_, fun i j hij => ?_, fun v g => ?_⟩, ⟨fun g i => ?_, hψ⟩, ?_, fun i j => ?_,
    fun g => rfl, fun g => rfl⟩
  · rw [hr, hr, ps, qs, s1, h.pol, ← low_pol]
  · rw [hr, hr, s1, h.pol, ← h.nor]
    exact low_diag _ _ _ _ _ _ i j hij
  · obtain ⟨α, β, γ, H⟩ := h.loc v
    have e : ∀ s, r (F.loc0 v s) = !![p (F.loc0 v s), 0, 0; (p (F.loc0 v s) - 1) * α, 1, 0;
        (p (F.loc0 v s) - q (F.loc0 v s)) * γ - (1 - q (F.loc0 v s)) * (α * β), (1 - q (F.loc0 v s)) * β,
        q (F.loc0 v s)] := fun s => by
      obtain ⟨h1, h2, h3⟩ := H s
      rw [hr, h1, h2, h3]
      simp only [Algebra.smul_def, map_sub, map_one]
      rfl
    have e0 : ∀ s, (ψ v 0 s : Q) = p (F.loc0 v s) := fun s => by rw [hψ, w0, zpow_one]; rfl
    have e1 : ∀ s, (ψ v 1 s : Q) = 1 := fun s => by rw [hψ, w1, zpow_zero]; simp
    have e2 : ∀ s, (ψ v 2 s : Q) = q (F.loc0 v s) := fun s => by rw [hψ, w2, _root_.zpow_neg_one]; rfl
    have := ord3 α β γ (p (F.loc0 v (g 0))) (q (F.loc0 v (g 0))) (p (F.loc0 v (g 1))) (q (F.loc0 v (g 1)))
      (p (F.loc0 v (g 2))) (q (F.loc0 v (g 2)))
    rw [← e, ← e, ← e] at this
    rw [ordProd, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
      List.prod_cons, List.prod_nil, mul_one]
    show (r _ - (ψ v 0 (g 0) : Q) • 1) * ((r _ - (ψ v 1 (g 1) : Q) • 1) * (r _ - (ψ v 2 (g 2) : Q) • 1)) = 0
    rw [e0, e1, e2]
    exact this
  · show r g i i = _
    rw [hr]
    fin_cases i
    · simp [w0, p]
    · simp [w1]
    · simp [w2, q]
  · refine Ideal.span_eq_bot.2 ?_
    rintro x ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    exact low_up _ _ _ _ _ i j hij
  · show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    exacts [lp, IsLocallyConstant.const 0, IsLocallyConstant.const 0, h.lcy, IsLocallyConstant.const 1,
      IsLocallyConstant.const 0, h.lca, lz, lq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NegOneZpowSg
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem neg_one_zpow_sg (K : Type) [CommRing K] (j : ℤ) :
    (((-1 : Kˣ) ^ j : Kˣ) : K) = sg K (j : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · rw [Even.neg_one_zpow (even_two_mul k)]
    push_cast
    rw [h2, zero_mul]
    simp [sg]
  · rw [Odd.neg_one_zpow (odd_two_mul_add_one k)]
    push_cast
    rw [h2, zero_mul, zero_add]
    show _ = (-1 : K) ^ 1
    simp

private theorem map_sg {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (j : ZMod 2) :
    f (sg K j) = sg K' j := by simp [sg]

private theorem sg_sq (K : Type) [CommRing K] (j : ZMod 2) : sg K j * sg K j = 1 := by
  rw [sg, ← mul_pow]; simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
  (S : Space O F 3)

private theorem ex_tau : ∃ τ : S.R →ₐ[O] S.R,
    (∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j) ∧
      ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g := by
  obtain ⟨ρ', h1, h2⟩ := alg_twist (-1 : S.Rˣ) S.ρ
  obtain ⟨⟨c1, c2⟩, ⟨b1, b2⟩, d⟩ := S.lift
  have hl : IsLift O ρ' := by
    refine ⟨⟨fun i j N => ?_, by rw [h2]; exact c2⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
    · simp only [h1, map_mul]
      exact (c1 i j N).comp (fun y => Ideal.Quotient.mk _ _ * y)
    · rw [NRep.map_r, h1, sub_self, zpow_zero, Units.val_one, one_mul]
      exact b1 g i
    · rw [NRep.map_ψ, h2]
      exact b2 v i g
    · rw [NRep.map_r, h1, map_mul]
      have := d g i j hij
      rw [NRep.map_r] at this
      rw [this, mul_zero]
  obtain ⟨τ, hτ, -⟩ := S.univ S.R ρ' hl
  refine ⟨τ, fun g i j => ?_, fun v i g => ?_⟩
  · rw [← h1, ← hτ]; rfl
  · conv_rhs => rw [← h2, ← hτ]
    rfl

private theorem tau_B (τ : S.R →ₐ[O] S.R)
    (h1 : ∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j)
    (h2 : ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g) : ∀ y ∈ S.B, τ y = y := by
  have hm : ∀ M : List (F.G0 × Fin 3 × Fin 3), τ (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod =
      (((-1 : S.Rˣ) ^ (M.map fun s => w 3 s.2.1 - w 3 s.2.2).sum : S.Rˣ) : S.R) *
        (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
    intro M
    induction M with
    | nil => simp
    | cons a M ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, h1, ih, _root_.zpow_add, Units.val_mul]
      ring
  have ha : ∀ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}), τ y = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨M, e, rfl⟩ | ⟨v, i, g, rfl⟩
      · rw [hm, e]; simp
      · exact h2 v i g
    | algebraMap r => exact τ.commutes r
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  have hloc : (maximalIdeal S.R).map τ ≤ maximalIdeal S.R := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  intro y hy
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal S.R) inferInstance _ fun N => ?_
  obtain ⟨z, hz, hyz⟩ := hy N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e : τ y - y = τ (y - z) - (y - z) := by rw [map_sub, ha z hz]; ring
  rw [e]
  refine sub_mem ?_ hyz
  have := Ideal.mem_map_of_mem τ hyz
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hloc N this

private theorem ex_tauA : ∃ τ : S.A →ₐ[O] S.A,
    (∀ g i j, τ (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j) ∧ (∀ y : S.B, τ (S.inc y) = S.inc y) ∧
      (∀ a, τ (τ a) = a) ∧ ∀ a, τ a - a ∈ S.u.ee := by
  obtain ⟨τ, h1, h2⟩ := ex_tau S
  have hB := tau_B S τ h1 h2
  have h1' : ∀ g i j, τ (S.ρ.r g i j) = sg S.R (pw i j) * S.ρ.r g i j := fun g i j => by
    rw [h1, neg_one_zpow_sg]; rfl
  have hA : ∀ y ∈ S.A, τ y ∈ S.A := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · rw [hB y hy]; exact S.B_le_A hy
      · rw [h1']
        exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (S.r_mem g i j)
    | algebraMap r => rw [τ.commutes r]; exact S.A.algebraMap_mem r
    | add a b _ _ ha hb => rw [map_add (f := τ)]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let τA : S.A →ₐ[O] S.A := (τ.comp S.A.val).codRestrict S.A fun a => hA a a.2
  have e1 : ∀ g i j, τA (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j := fun g i j =>
    Subtype.ext ((h1' g i j).trans (by
      rw [← map_sg (S.A.val : S.A →+* S.R)]; rfl))
  have e2 : ∀ y : S.B, τA (S.inc y) = S.inc y := fun y => Subtype.ext (hB y y.2)
  have ind : ∀ P : S.A → Prop, (∀ y : S.B, P (S.inc y)) → (∀ g i j, P (S.u.r g i j)) →
      (∀ a b, P a → P b → P (a + b)) → (∀ a b, P a → P b → P (a * b)) → ∀ a, P a := by
    intro P p1 p2 p3 p4 ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact p1 ⟨y, hy⟩
      · exact p2 g i j
    | algebraMap r => exact p1 (algebraMap O S.B r)
    | add a b ha hb qa qb => exact p3 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
    | mul a b ha hb qa qb => exact p4 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
  refine ⟨τA, e1, e2, ind _ (fun y => by rw [e2, e2]) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_,
    ind _ (fun y => by rw [e2, sub_self]; exact zero_mem _) (fun g i j => ?_) (fun a b qa qb => ?_)
      fun a b qa qb => ?_⟩
  · rw [e1, map_mul, e1, ← mul_assoc]
    have := map_sg (τA : S.A →+* S.A) (pw i j)
    rw [RingHom.coe_coe] at this
    rw [this, sg_sq, one_mul]
  · rw [map_add (f := _), map_add (f := _), qa, qb]
  · rw [map_mul, map_mul, qa, qb]
  · rw [e1, pw, ← neg_one_zpow_sg]
    rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
    · rw [h.neg_one_zpow]; simp
    · exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
        (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  · rw [map_add (f := _), add_sub_add_comm]; exact add_mem qa qb
  · have : τA (a * b) - a * b = (τA a - a) * τA b + a * (τA b - b) := by rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ qa) (Ideal.mul_mem_left _ _ qb)

end

theorem UpperTheory.V.Fr.ep_inv :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∃ σ, L.IsInv σ := by
  intro l _ O _ _ _ _ F C₀ _ S x L hx
  obtain ⟨τ, h1, h2, h3, h4⟩ := ex_tauA S
  obtain ⟨σ, hσ, -⟩ := L.univ L.R (L.ι.comp τ) fun a => by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff, AlgHom.comp_apply, ← map_sub]
    have := hx (h4 a)
    rw [← L.lies] at this
    exact this
  obtain ⟨g₀, -, hu⟩ := L.univ L.R L.ι fun _ => rfl
  have hsq : σ.comp σ = AlgHom.id _ _ :=
    (hu (σ.comp σ) fun a => by
      rw [AlgHom.comp_apply, hσ, AlgHom.comp_apply, hσ, AlgHom.comp_apply, h3]).trans
      (hu (AlgHom.id _ _) fun _ => rfl).symm
  refine ⟨σ, fun y => DFunLike.congr_fun hsq y, fun g a b => ?_, fun y => ?_⟩
  · show σ (L.ι (S.u.r g a b)) = sg _ _ * L.ι (S.u.r g a b)
    rw [hσ, AlgHom.comp_apply, h1, map_mul, ← map_sg (L.ι : S.A →+* L.R)]
    rfl
  · show σ (L.ι (S.inc y)) = sg _ _ * L.ι (S.inc y)
    rw [hσ, AlgHom.comp_apply, h2]
    simp [sg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NontrivTr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rank_tr {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G]
    [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ)
    (χ' : G →* Kˣ) (h : ∀ g, χ' g = Units.map f.toMonoidHom (χ g)) :
    Module.rank K (H1C loc (chRep χ') fun _ => ⊥) = Module.rank k (H1C loc (chRep χ) fun _ => ⊥) ∧
    Module.rank K (H1C loc (chRep χ') fun _ => ⊤) = Module.rank k (H1C loc (chRep χ) fun _ => ⊤) := by
  have hχ : χ' = (Units.map (f : k →* K)).comp χ := MonoidHom.ext fun g => h g
  subst hχ
  exact ⟨(n4ch f loc χ (fun _ => ⊥) (fun _ => ⊥) (fun _ => Or.inl ⟨rfl, rfl⟩)).2,
    (n4ch f loc χ (fun _ => ⊤) (fun _ => ⊤) (fun _ => Or.inr ⟨rfl, rfl⟩)).2⟩

private theorem nontriv_tr {k K M N : Type} [Field k] [Field K] [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module K N] (e : Module.rank K N = Module.rank k M) (h : Nontrivial M) : Nontrivial N := by
  rw [← rank_pos_iff_nontrivial (R := K), e]
  exact rank_pos_iff_nontrivial.2 h

theorem UpperTheory.V.Fr.ok_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {k' : Type} [Field k'] [Finite k'] [CharP k' l] (f : k →+* k'), F.Ok C₀ → (F.ext f).Ok C₀ := by
  intro l _ k _ _ F C₀ k' _ _ _ f h
  have hinj : Function.Injective f := f.injective
  have hU : ∀ u v : kˣ, Units.map (f : k →* k') u = Units.map (f : k →* k') v → u = v := by
    intro u v huv
    ext
    apply hinj
    simpa using congrArg Units.val huv
  have hU1 : ∀ u : kˣ, Units.map (f : k →* k') u = 1 → u = 1 := by
    intro u hu
    apply hU
    rw [hu, map_one]
  have hΨ : ∀ g, (F.ext f).Ψ g = Units.map (f : k →* k') (F.Ψ g) := fun g => rfl
  have hz : ∀ x : ZMod l, f (ZMod.castHom (dvd_refl l) k x) = ZMod.castHom (dvd_refl l) k' x :=
    fun x => RingHom.congr_fun
      (Subsingleton.elim (f.comp (ZMod.castHom (dvd_refl l) k)) (ZMod.castHom (dvd_refl l) k')) x
  have hom : ∀ g, (F.ext f).om k' g = Units.map (f : k →* k') (F.om k g) := by
    intro g
    ext
    change ((ZMod.castHom (dvd_refl l) k').comp PadicInt.toZMod) ((F.eps g : ℤ_[l])) =
      f (((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) ((F.eps g : ℤ_[l])))
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (hz _).symm
  have hdel : ∀ g, (F.ext f).delK k' g = Units.map (f : k →* k') (F.delK k g) := by
    intro g
    ext
    change (Int.castRingHom k') (F.del g : ℤ) = f ((Int.castRingHom k) (F.del g : ℤ))
    simp
  have hker : (F.ext f).Ψ.ker = F.Ψ.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨hU1 _, fun h1 => by rw [hΨ, h1, map_one]⟩
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ h.del_open).isCompact
  have hχ1 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ * F.delK k) g) := by
    intro g
    change ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g = Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_inv]
    rfl
  have hχ2 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ ^ 2 * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ ^ 2 * F.delK k) g) := by
    intro g
    rw [pow_two, pow_two]
    change ((F.ext f).Ψ g)⁻¹ * ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g =
      Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * (F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_mul, map_inv]
    rfl
  have hχ3 : ∀ g : F.G0, ((F.ext f).Ψ⁻¹.comp (F.ext f).del.ker.subtype) g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹.comp F.del.ker.subtype) g) := by
    intro g
    change (Units.map (f : k →* k') (F.Ψ (g : F.Γ)))⁻¹ = Units.map f.toMonoidHom ((F.Ψ (g : F.Γ))⁻¹)
    rw [map_inv]
    rfl
  have hχ4 : ∀ g : F.Γ, (1 : F.Γ →* k'ˣ) g = Units.map f.toMonoidHom ((1 : F.Γ →* kˣ) g) := by
    intro g
    rw [MonoidHom.one_apply, MonoidHom.one_apply, map_one]
  exact
    { l_odd := h.l_odd
      fin := inferInstance
      del_open := h.del_open
      c_sq := h.c_sq
      del_c := h.del_c
      loc_cont := h.loc_cont
      eps_cont := h.eps_cont
      Ψ_open := by rw [hker]; exact h.Ψ_open
      Ψ_c := by
        show Units.map (f : k →* k') (F.Ψ F.c) = 1
        rw [h.Ψ_c, map_one]
      baseSubgroup_spec := fun he => h.baseSubgroup_spec (hU1 _ (by rw [map_pow]; exact he))
      phi := h.phi
      card_inf := h.card_inf
      cw_sq := h.cw_sq
      del_cw := h.del_cw
      f2a := by
        obtain ⟨g, hg⟩ := h.f2a
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom] at he
        exact he
      f2b := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2b j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom, hΨ] at he
        rw [map_mul, map_zpow]
        exact he
      f2c := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2c j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        erw [hom, hdel] at he
        rw [map_mul, map_mul, map_zpow]
        exact he
      f3 := by
        intro v
        obtain ⟨g, hg⟩ := h.f3 v
        exact ⟨g, fun he => hg (hU1 _ (by rw [map_pow]; exact he))⟩
      f4 := nontriv_tr (rank_tr f F.loc _ _ hχ1).1 h.f4
      f4' := nontriv_tr (rank_tr f F.loc _ _ hχ2).1 h.f4'
      f5 := by
        rintro ⟨j, hj⟩
        refine h.f5 ⟨j, fun g => hU _ _ ?_⟩
        have hg := hj g
        rw [hom, hΨ] at hg
        rw [map_zpow]
        exact hg
      Ψ_N := fun v g hg => by
        show Units.map (f : k →* k') (F.Ψ (F.loc v g)) = 1
        rw [h.Ψ_N v g hg, map_one]
      gen := by
        intro v
        obtain ⟨u, a₀, h1, h2, h3⟩ := h.gen v
        refine ⟨u, a₀, fun a => ⟨(h1 a).1, ?_⟩, h2, h3⟩
        show Units.map (f : k →* k') (F.Ψ (F.loc v (u a))) = 1
        rw [(h1 a).2, map_one]
      cl := h.cl
      ec := h.ec
      b1p := (rank_tr f F.loc _ _ hχ2).1.trans_le h.b1p
      b1 := (rank_tr f F.loc2 _ _ hχ3).1.trans_le h.b1
      h1 := (rank_tr f F.loc _ _ hχ4).2.trans_le h.h1 }
end

