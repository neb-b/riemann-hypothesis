module

public import ReciprocityTheory.DualLattices.Bundle0020
public import ReciprocityTheory.DualLattices.TotalFibreMapTotalFibreNsmulSnd
public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.OneAddPowOfSq
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add (f := _)] at ha hb ⊢
    rw [ha, hb]

private lemma one_add_pow_of_sq {S : Type*} [CommRing S] (a : S) (ha : a * a = 0) (k : ℕ) :
    (1 + a) ^ k = 1 + k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : S) * ha

theorem b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by
  intro Dp ι τ E ht bt h1 h2 h3 i j
  apply sub_eq_zero.mp
  apply Tw.sep
  intro n
  obtain ⟨k, hk, hpair⟩ := h1 i j n
  obtain ⟨thi, wi, hmi, hNi, hwi⟩ := h3 i n
  obtain ⟨thj, wj, hmj, hNj, hwj⟩ := h3 j n
  have hsurjL : Function.Surjective (Tw.π n).1.toLinearMap := Tw.surj n
  obtain ⟨hsi, hsi_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL
  obtain ⟨hsj, hsj_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  have hpq := hnat _ _ (Tw.q n) _ _ _ _ hpair
  rw [← hmi, ← hmj] at hpq
  have hB3' := hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n)
    (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj)
    hsi hsj (Tw.zh n ^ k) _ hNi hNj
    (by rw [hmi, hsi_spec]; exact h2 i n) (by rw [hmj, hsj_spec]; exact h2 j n) hpq
    (Units.ext (by simp [Tw.ζ_spec]))
  have hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) =
        Tw.ξ n * B.ev h w := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp [BX.evK, BX.ev]
    | tmul g r =>
      simp [BX.evK, BX.ev, ξmul]
      ring
    | add a b ha hb =>
      simp only [BX.evK, BX.ev, map_add (f := _)] at ha hb ⊢
      rw [ha, hb, mul_add]
  rw [hev, hev] at hB3'
  have hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) =
      1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n) := by
    rw [Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]
    apply one_add_pow_of_sq
    calc Tw.cp n * Tw.ξ n * (Tw.cp n * Tw.ξ n) = Tw.cp n * Tw.cp n * (Tw.ξ n * Tw.ξ n) := by ring
      _ = 0 := by rw [Tw.ξ_sq n, mul_zero]
  have hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0 := by
    have hh := hB3'.symm.trans hpow
    linear_combination -hh
  have hmem := Tw.ann n _ hξ
  rw [← Tw.ker_eq n, RingHom.mem_ker] at hmem
  have e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i)) := by
    rw [BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]
  have e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j)) := by
    rw [BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]
  simp only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem
  rw [map_sub, map_sub, map_mul, hk]
  linear_combination hmem

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.TangentPairingStatementOfHeightFunctional
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

theorem tangentPairingStatement_of_heightFunctional (hB2 : HighestWeightVectorUniformBounds B) : TangentPairingStatement B := by
  intro R' R π ξ Dp N hsurj hker hsq _ hN sh th Vs Vt hs ht zh z hsV htV hhs hht hpair hz
  have hπ : π.SqZero := π.sqZero_of_span ξ hsurj hker hsq
  obtain ⟨O, hOsw, hO⟩ := B.step1 π Dp ξ hsurj hker hsq hB2 N hN
  obtain ⟨hsN, htN, u0, l1, l2, h1, h2, hz'⟩ := hpair
  obtain ⟨l⟩ := B.nonempty R' sh th
  obtain ⟨μ, hμ⟩ := B.exists_smul (B.pmap π l) u0
  obtain ⟨μ', hμ'⟩ := π.exists_unit_lift hsurj μ
  obtain ⟨a1, ha1⟩ := π.exists_unit_lift hsurj l1
  obtain ⟨a2, ha2⟩ := π.exists_unit_lift hsurj l2
  obtain ⟨l', hl⟩ : ∃ l' : B.P R' sh th, B.pmap π l' = u0 :=
    ⟨B.smul μ' l, by rw [B.pmap_smul, hμ', hμ]⟩
  have htg0 : ∀ V, B.map π (B.tg π hπ V) = 0 := fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩
  have hinv1 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a1⁻¹ * l1 = 1 := by
    rw [map_inv, ha1, inv_mul_cancel]
  have hinv2 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a2⁻¹ * l2 = 1 := by
    rw [map_inv, ha2, inv_mul_cancel]

  have hu : HEq (B.pmap π (B.smul a1⁻¹ (B.tr1 hsV (B.nsmul1 l' N))))
      (B.zero1 (B.map π th)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr1 hsV (B.nsmul1 l' N))) (B.smul l1 (B.zero1 (B.map π th))) := by
      refine (B.pmap_hcongr π hsV.symm rfl (B.castFst_heq hsV _)).trans ?_
      refine (B.pmap_nsmul1 π _ N).trans ?_
      rw [hl, ← h1]
      exact (B.castFst_heq hsN _).symm
    refine (B.smul_hcongr (htg0 Vs) rfl _ e).trans ?_
    rw [← B.mul_smul, hinv1, B.one_smul]
  have hu'0 : HEq (B.pmap π (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))))
      (B.zero2 (B.map π sh)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr2 htV (B.nsmul2 l' N))) (B.smul l2 (B.zero2 (B.map π sh))) := by
      refine (B.pmap_hcongr π rfl htV.symm (B.castSnd_heq htV _)).trans ?_
      refine (B.pmap_nsmul2 π _ N).trans ?_
      rw [hl, ← h2]
      exact (B.castSnd_heq htN _).symm
    refine (B.smul_hcongr rfl (htg0 Vt) _ e).trans ?_
    rw [← B.mul_smul, hinv2, B.one_smul]
  have hu' : HEq (B.pmap π (B.sw (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N)))))
      (B.zero1 (B.map π sh)) := by
    rw [← B.sw_nat]
    refine (B.sw_hcongr rfl (htg0 Vt) hu'0).trans ?_
    rw [B.sw_zero2]
  obtain ⟨ct, hct, hNt⟩ := hO Vs Vt th ht htV hht _ hu
  obtain ⟨cs, hcs, hNs⟩ := hO Vt Vs sh hs hsV hhs _ hu'

  have k1 : HEq (B.smul (a1⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul ct (O Vs Vt)) := by
    refine HEq.trans ?_ ((B.castSnd_heq htV _).symm.trans (heq_of_eq hNt))
    rw [B.nsmul2_smul]
    exact B.smul_hcongr hsV rfl _ (B.nsmul2_hcongr hsV rfl N (B.castFst_heq hsV _).symm)
  have k2 : HEq (B.smul (a2⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul cs (O Vs Vt)) := by
    have s1 : HEq (B.sw (B.nsmul1 (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))) N))
        (B.smul cs (O Vt Vs)) := by
      rw [B.sw_nsmul1]; exact (B.castSnd_heq hsV _).symm.trans (heq_of_eq hNs)
    have s2 := B.sw_hcongr rfl hsV s1
    rw [B.sw_sw, B.sw_smul, hOsw] at s2
    refine HEq.trans ?_ s2
    rw [B.nsmul1_smul, B.nsmul_comm]
    exact B.smul_hcongr rfl htV _ (B.nsmul1_hcongr rfl htV N (B.castSnd_heq htV _).symm)
  obtain ⟨X₀, hX₀⟩ := B.exists_cast hsV htV (B.nsmul2 (B.nsmul1 l' N) N)
  have e1 : B.smul (a1⁻¹ ^ N) X₀ = B.smul ct (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k1)
  have e2 : B.smul (a2⁻¹ ^ N) X₀ = B.smul cs (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k2)
  have hX1 : X₀ = B.smul (a1 ^ N * ct) (O Vs Vt) := by
    rw [B.mul_smul, ← e1, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have hX2 : X₀ = B.smul (a2 ^ N * cs) (O Vs Vt) := by
    rw [B.mul_smul, ← e2, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have key : a1 ^ N * ct = a2 ^ N * cs := B.smul_inj (hX1.symm.trans hX2)

  have hν : Units.map (π.1 : (R' : Type u) →* (R : Type u)) (zh * a2 * a1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hz, ha1, ha2, hz', div_mul_cancel, mul_inv_cancel]
  have hνN := LHom.pow_eq_one hπ hN (zh * a2 * a1⁻¹)
    (by have := congrArg Units.val hν; simpa using this)
  have hz1 : zh ^ N * a2 ^ N = a1 ^ N := by
    rw [mul_pow, mul_pow, inv_pow] at hνN
    exact mul_inv_eq_one.1 hνN
  have hz2 : zh ^ N * ct = cs := by
    have h3 : a2 ^ N * (zh ^ N * ct) = a2 ^ N * cs := by
      rw [← key, ← hz1]; ac_rfl
    exact mul_left_cancel h3
  have hA : π.1 (B.evK π ht Vs) = 0 := (RingHom.mem_ker).1 (evalT_mem ht (RingHom.ker π.1) Vs)
  have hB : π.1 (B.evK π hs Vt) = 0 := (RingHom.mem_ker).1 (evalT_mem hs (RingHom.ker π.1) Vt)
  have hAA := LHom.mul_eq_zero hπ hA hA
  have hAB := LHom.mul_eq_zero hπ hA hB
  have h4 := congrArg Units.val hz2
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hct, hcs] at h4
  linear_combination (1 + B.evK π ht Vs) * h4 + (zh : (R' : Type u)) ^ N * hAA - hAB

end BX

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ThmAUses
section
noncomputable section

open Matrix TensorProduct

namespace ReciprocityTheory.PGsh

section Mat

variable {D : Type} [CommRing D] {g : ℕ}

lemma stdJ_mul_self : stdJ D g * stdJ D g = -1 := by
  ext (i | i) (j | j) <;> simp [stdJ, Matrix.fromBlocks_multiply, Matrix.one_apply]

lemma det_stdJ_sq : (stdJ D g).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, stdJ_mul_self, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul]
  simp

lemma isUnit_det_stdJ : IsUnit (stdJ D g).det := by
  exact isUnit_iff_exists_inv.2 ⟨(stdJ D g).det, by rw [← sq, det_stdJ_sq]⟩

lemma det_sq_eq (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_sum, Fintype.card_fin,
    ← two_mul] at h
  have hJ2 := det_stdJ_sq (D := D) (g := g)
  calc Φ.det ^ 2 = Φ.det ^ 2 * ((stdJ D g).det ^ 2) := by rw [hJ2, mul_one]
    _ = (Φ.det * (stdJ D g).det * Φ.det) * (stdJ D g).det := by ring
    _ = c ^ (2 * g) * (E.det * (stdJ D g).det) := by rw [h]; ring

end Mat

section Span

variable {R₀ : Type} [CommRing R₀]

end Span

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Val

end ReciprocityTheory.PGsh
end
end

