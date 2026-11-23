module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GrOfKill

theorem exists_unit_one_add (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by
  have hu : IsUnit (((1 + l : ℕ) : ℤ_[l])) := by
    push_cast
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  exact ⟨hu.unit, rfl⟩

theorem gr_of_vanish_on_trivial : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  intro l _ Ω _ _ _ e S A W hW y hy hN
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have hmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by simp [mat]
  have hone : mat W 1 = 1 := by simp [mat]
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have h11 : ∀ s t, s ∈ D → mat W (s * t) 1 1 = mat W s 1 1 * mat W t 1 1 := by
    intro s t hs; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring
  have h01 : ∀ s t, t ∈ D → mat W (s * t) 0 1 = mat W s 0 0 * mat W t 0 1 + mat W s 0 1 * mat W t 1 1 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two]
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t := fun s t => by
    have := hy.2 s t
    rw [this]; rfl
  have hy1 : y 1 = 0 := by
    have := hcoc 1 1
    simpa [hone] using this
  have hb : ∀ s t, s ∈ D → y (s * t) 1 = y s 1 + mat W s 1 1 * y t 1 := by
    intro s t hs; rw [hcoc]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]

  let P : G ℚ Ω → Prop := fun u => u ∈ D ∧ mat W u 0 0 = 1 ∧ mat W u 1 1 = 1 ∧ cycBar ℚ Ω l u = 1

  have hfac : ∀ u v, P u → P v → mat W u 0 1 = mat W v 0 1 → y u = y v := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩ h
    have hm : mat W u = mat W v := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hu0, hv0]
      · exact h
      · simp [hup u huD, hup v hvD]
      · simp [hu1, hv1]
    have hW' : W u = W v := Units.ext hm
    have hn : u⁻¹ * v ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · simp [MonoidHom.mem_ker, map_mul, map_inv, huc, hvc]
      · simp [MonoidHom.mem_ker, map_mul, map_inv, hW']
    have e1 : v = u * (u⁻¹ * v) := by group
    rw [e1, hcoc, hN _ hn, Matrix.mulVec_zero, add_zero]
  have hPmul : ∀ u v, P u → P v → P (u * v) ∧ mat W (u * v) 0 1 = mat W u 0 1 + mat W v 0 1 ∧
      y (u * v) 1 = y u 1 + y v 1 := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩
    refine ⟨⟨D.mul_mem huD hvD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 u v hvD, hu0, hv0, one_mul]
    · rw [h11 u v huD, hu1, hv1, one_mul]
    · rw [map_mul, huc, hvc, one_mul]
    · rw [h01 u v hvD, hu0, hv1]; ring
    · rw [hb u v huD, hu1, one_mul]
  have hPpow : ∀ u, P u → ∀ n : ℕ, P (u ^ n) ∧ mat W (u ^ n) 0 1 = n * mat W u 0 1 ∧
      y (u ^ n) 1 = n * y u 1 := by
    intro u hu n
    induction n with
    | zero =>
      refine ⟨⟨D.one_mem, by simp [hone], by simp [hone], by simp⟩, by simp [hone], by simp [hy1]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := hPmul _ _ ih.1 hu
      rw [pow_succ]
      refine ⟨h1, ?_, ?_⟩
      · rw [h2, ih.2.1]; push_cast; ring
      · rw [h3, ih.2.2]; push_cast; ring

  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdet : mat W T 0 0 * mat W T 1 1 = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have hdT : dt W T = 1 := by
      rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h3 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [hdT, Units.val_one, Matrix.det_fin_two, hup T hTD] at h3
    linear_combination -h3
  have hNqne : ∀ k : ℕ, 1 ≤ k → ((Nq ^ k : ℕ) : Qbar l) ≠ 1 := by
    intro k hk h
    have h' : Nq ^ k = 1 := by exact_mod_cast h
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hpos : 2 * (e * m) ≠ 0 := by
      have := hW.e_pos; positivity
    have : 1 < Nq ^ k := by
      rw [hNq, ← pow_mul]
      exact Nat.one_lt_pow (by positivity) (by omega)
    omega
  have hTi : T * T⁻¹ = 1 := mul_inv_cancel T
  have hTiD : T⁻¹ ∈ D := D.inv_mem hTD
  have hTi11 : mat W T⁻¹ 1 1 = (Nq : Qbar l) := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone] at this
    rw [Matrix.one_apply_eq] at this
    linear_combination (-(mat W T⁻¹ 1 1)) * hdet - (mat W T 0 0) * this + hT00
  have hi11 : mat W T 1 1 * mat W T⁻¹ 1 1 = 1 := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinvy : y T 1 + mat W T 1 1 * y T⁻¹ 1 = 0 := by
    have := hb T T⁻¹ hTD
    rw [hTi, hy1] at this
    simpa using this.symm

  have hPconj : ∀ u, P u → P (T * u * T⁻¹) ∧ mat W (T * u * T⁻¹) 0 1 = ((Nq * Nq : ℕ) : Qbar l) * mat W u 0 1 ∧
      y (T * u * T⁻¹) 1 = mat W T 1 1 * y u 1 := by
    rintro u ⟨huD, hu0', hu1, huc⟩
    have hTuD : T * u ∈ D := D.mul_mem hTD huD
    have hi00 : mat W T 0 0 * mat W T⁻¹ 0 0 = 1 := by
      have := h00 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_eq] at this
      exact this.symm
    have hi01 : mat W T 0 0 * mat W T⁻¹ 0 1 + mat W T 0 1 * mat W T⁻¹ 1 1 = 0 := by
      have := h01 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_ne (by decide)] at this
      exact this.symm
    refine ⟨⟨D.mul_mem hTuD hTiD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 _ _ hTiD, h00 _ _ huD, hu0', mul_one, hi00]
    · rw [h11 _ _ hTuD, h11 _ _ hTD, hu1, mul_one, hi11]
    · simp [map_mul, map_inv, huc]
    · rw [h01 _ _ hTiD, h01 _ _ huD, h00 _ _ huD, hu0', hu1]
      push_cast
      linear_combination hi01 + mat W u 0 1 * mat W T⁻¹ 1 1 * hT00 + mat W u 0 1 * (Nq : Qbar l) * hTi11
    · rw [mul_assoc, hb T _ hTD, hb u T⁻¹ huD, hu1]
      linear_combination hinvy

  have hvan : ∀ u, P u → y u 1 = 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hc3⟩ := hPconj u hu
    obtain ⟨hp1, hp2, hp3⟩ := hPpow u hu (Nq * Nq)
    have h3 := hfac _ _ hc1 hp1 (by rw [hc2, hp2])
    have h4 : mat W T 1 1 * y u 1 = ((Nq * Nq : ℕ) : Qbar l) * y u 1 := by rw [← hc3, ← hp3, h3]
    have h5 : (((Nq ^ 3 : ℕ) : Qbar l) - 1) * y u 1 = 0 := by
      push_cast at h4 ⊢
      linear_combination (-(Nq : Qbar l)) * h4 + y u 1 * hdet - y u 1 * mat W T 1 1 * hT00
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (sub_eq_zero.1 h) (hNqne 3 (by norm_num))
    · exact h

  have hT11ne : mat W T 1 1 - 1 ≠ 0 := by
    intro h
    have h' : mat W T 1 1 = 1 := sub_eq_zero.1 h
    rw [h', mul_one, hT00] at hdet
    exact hNqne 1 (by norm_num) (by simpa using hdet)
  refine ⟨y T 1 / (mat W T 1 1 - 1), fun s hs => ?_⟩
  have hsT : s * T ∈ D := D.mul_mem hs hTD
  have hTs : T * s ∈ D := D.mul_mem hTD hs
  have hsTi : (s * T)⁻¹ ∈ D := D.inv_mem hsT
  have hinv00 : mat W (s * T)⁻¹ 0 0 * mat W (s * T) 0 0 = 1 := by
    have := h00 (s * T)⁻¹ (s * T) hsT
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinv11 : mat W (s * T)⁻¹ 1 1 * mat W (s * T) 1 1 = 1 := by
    have := h11 (s * T)⁻¹ (s * T) hsTi
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hcP : P ((s * T)⁻¹ * (T * s)) := by
    refine ⟨D.mul_mem hsTi hTs, ?_, ?_, ?_⟩
    · rw [h00 _ _ hTs, h00 _ _ hs]
      linear_combination hinv00 - mat W (s * T)⁻¹ 0 0 * h00 s T hTD
    · rw [h11 _ _ hsTi, h11 _ _ hTD]
      linear_combination hinv11 - mat W (s * T)⁻¹ 1 1 * h11 s T hs
    · have hcs : cycBar ℚ Ω l (T * s) = cycBar ℚ Ω l (s * T) := by rw [map_mul, map_mul, mul_comm]
      rw [map_mul, map_inv, hcs, inv_mul_cancel]
  have hyc := hvan _ hcP
  have e1 : (s * T) * ((s * T)⁻¹ * (T * s)) = T * s := by group
  have h6 := hb (s * T) ((s * T)⁻¹ * (T * s)) hsT
  rw [e1, hyc, mul_zero, add_zero, hb T s hTD, hb s T hs] at h6
  have hinv := mul_inv_cancel₀ hT11ne
  rw [div_eq_mul_inv]
  linear_combination (mat W T 1 1 - 1)⁻¹ * h6 - y s 1 * hinv

end GlobalTheory.Ord2.GrOfKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvariance
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

private theorem commHt_norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral ..)

theorem commHt_norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  commHt_norm_le_one_of_isIntegral l x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem commHt_cocycle_mulVec (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat V s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

theorem commHt_cocycle_commutator (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (a b : G ℚ Ω)
    (ha : V a = 1) (hb : V b = 1) : x (a * b * a⁻¹ * b⁻¹) = 0 := by
  have hm := commHt_cocycle_mulVec V hx
  have m1 : ∀ s, V s = 1 → mat V s = 1 := fun s hs => by simp [mat, hs]
  have h1 : x 1 = 0 := by
    have := hm 1 1
    rw [m1 1 (map_one V), Matrix.one_mulVec, mul_one] at this
    simpa using this
  have hinv : ∀ s, V s = 1 → x s⁻¹ = - x s := by
    intro s hs
    have := hm s s⁻¹
    rw [mul_inv_cancel, h1, m1 s hs, Matrix.one_mulVec] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hai : V a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
  have hab : V (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have haba : V (a * b * a⁻¹) = 1 := by rw [map_mul, hab, hai, one_mul]
  rw [hm, m1 _ haba, Matrix.one_mulVec, hm, m1 _ hab, Matrix.one_mulVec, hm, m1 _ ha, Matrix.one_mulVec,
    hinv a ha, hinv b hb]
  abel

theorem commHt_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, tw, hw, hc, hd]

theorem ht_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  intro l _ Ω _ _ _ n c W y z u hO hy hz hu φ hφ g hg h hh
  have hk : g * h * g⁻¹ * h⁻¹ ∈ N0g W :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  set k := g * h * g⁻¹ * h⁻¹ with hkdef
  have kerW : ∀ s ∈ N0g W, W s = 1 := fun s hs => (Subgroup.mem_inf.1 hs).2
  have epsN : ∀ s ∈ N0g W, eps l s = 1 := fun s hs => by
    have := (Subgroup.mem_inf.1 hs).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have epsφ : eps l φ = 1 := by
    have := (Subgroup.mem_inf.1 hφ).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have matN : ∀ s ∈ N0g W, mat W s = 1 := fun s hs => by simp [mat, kerW s hs]
  have matD : ∀ s ∈ N0g W, mat (dual1 W) s = 1 := fun s hs => by simp [mat, commHt_dual1_eq_one hs]
  have hyk : y k = 0 := commHt_cocycle_commutator W hy g h (kerW g hg) (kerW h hh)
  have hzk : z k = 0 := commHt_cocycle_commutator (dual1 W) hz g h (commHt_dual1_eq_one hg) (commHt_dual1_eq_one hh)
  have hmat : mat W (φ * k) = mat W φ := by simp [mat, map_mul, kerW k hk]
  have hyφ : y (φ * k) = y φ := by rw [commHt_cocycle_mulVec W hy, hyk, Matrix.mulVec_zero, add_zero]
  have hzφ : z (φ * k) = z φ := by rw [commHt_cocycle_mulVec (dual1 W) hz, hzk, Matrix.mulVec_zero, add_zero]
  have hdiff : ht W y z u (φ * k) - ht W y z u φ = (mat W φ - 1).det * (u (φ * k) - u φ) := by
    simp only [ht, hmat, hyφ, hzφ]; ring
  have hkhg : k * (h * g) = g * h := by simp only [hkdef]; group

  set E : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W y z s t - (eps l s * u t - u (s * t) + u s) with hEdef
  have hE : ∀ s t, ‖E s t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun s t => hu s t
  have c1 : cup W y z φ k = 0 := by simp [cup, hzk, om]
  have c2 : cup W y z k (h * g) = 0 := by simp [cup, hyk, om]
  have c3 : cup W y z g h = om (y g) (z h) := by simp [cup, matD g hg]
  have c4 : cup W y z h g = om (y h) (z g) := by simp [cup, matD h hh]
  have key : (u (φ * k) - u φ) - (om (y h) (z g) - om (y g) (z h)) =
      E φ k + E g h - E h g - E k (h * g) := by
    simp only [hEdef, c1, c2, c3, c4, hkhg, epsφ, epsN k hk, epsN g hg, epsN h hh]
    ring
  have hdet : ‖(mat W φ - 1).det‖ ≤ 1 := by
    apply commHt_norm_le_one_of_mem c
    rw [Matrix.det_fin_two]
    have he : ∀ i j, (mat W φ - 1) i j ∈ c.O := by
      intro i j
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem (hO φ i j) (one_mem _)
      · exact sub_mem (hO φ i j) (zero_mem _)
    exact sub_mem (mul_mem (he 0 0) (he 1 1)) (mul_mem (he 0 1) (he 1 0))
  have hsum : ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have hs : ∀ a b : Qbar l, ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ →
        ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun a b ha hb => by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
    exact hs _ _ (hs _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE _ _) (hE _ _))) (hE _ _)) (hE _ _)
  unfold Cg
  rw [hdiff, ← mul_sub, norm_mul, key]
  calc ‖(mat W φ - 1).det‖ * ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hdet hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesRootOfUnity
section
namespace GlobalTheory.InertiaRootOfUnity

theorem eq_one_of_val_sub_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (N : ℕ) (hN : ¬ w (N : K) < 1) (u : K) (hu : u ^ N = 1) (h : w (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hw1 : w u = 1 := by
    have h' := Valuation.map_add_eq_of_lt_right w (x := u - 1) (y := 1) (by rw [map_one]; exact h)
    rwa [sub_add_cancel, map_one] at h'
  have hpow : ∀ i : ℕ, w (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [hr]
      refine Valuation.map_add_lt w ?_ h
      rw [map_mul, hw1, one_mul]
      exact ih
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have hg := geom_sum_mul u N
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hx
  have hNeq : (N : K) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  apply hN
  rw [hNeq, Valuation.map_neg]
  exact w.map_sum_lt one_ne_zero fun i _ => hpow i

theorem inertia_fixes_root_of_unity {Ω : Type} [Field Ω] [Algebra ℚ Ω] (N : ℕ) (v : GlobalTheory.Ord2.Pl)
    (B : ValuationSubring Ω) (hB : Formalism.ConjugateSelfDual.IsPlaceOver B v)
    (hN : ¬ ((N : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal))
    (s : Formalism.ConjugateSelfDual.G ℚ Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine B) (ζ : Ω) (hζ : ζ ^ N = 1) : s ζ = ζ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simpa using v.asIdeal.zero_mem)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hN0] at hζ
  have hwζ : B.valuation ζ = 1 := by
    have hp : B.valuation ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (B.valuation ζ) 1 with hlt | heq | hgt
    · exact absurd hp (pow_lt_one₀ zero_le' hlt hN0).ne
    · exact heq
    · exact absurd hp (one_lt_pow₀ hgt hN0).ne'
  have hI := (ReciprocityTheory.Gal.mem_Ine.mp hs).2 ζ hwζ.le
  have hsζ : s ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
  have hone := eq_one_of_val_sub_lt B.valuation N ?_ (s ζ * ζ⁻¹) ?_ ?_
  · exact (mul_inv_eq_one₀ hζ0).mp hone
  · intro hlt
    exact hN ((hB N).mp (by simpa using hlt))
  · rw [mul_pow, hsζ, inv_pow, hζ, inv_one, mul_one]
  · have hr : s ζ * ζ⁻¹ - 1 = (s ζ - ζ) * ζ⁻¹ := by field_simp
    rw [hr, map_mul, map_inv₀, hwζ, inv_one, mul_one]
    exact hI

end GlobalTheory.InertiaRootOfUnity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lipschitz_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  intro l hl Γ _ P lam hmono hsmall hdec
  obtain ⟨m₀, hdec⟩ := hdec
  have hmono' : ∀ a b g, P (a + b) g → P a g := by
    intro a b g h
    induction b with
    | zero => simpa using h
    | succ b ih => exact ih (hmono _ _ h)
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl.out.pos
  have key : ∀ x y : Γ, ‖(lam (x ^ l * y)).toAdd‖ ≤
      max ((l:ℝ)⁻¹ * ‖(lam x).toAdd‖) ‖(lam y).toAdd‖ := by
    intro x y
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow]
    refine (PadicInt.nonarchimedean _ _).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, norm_mul, PadicInt.norm_p]
  have step : ∀ m, m₀ ≤ m → ∀ t : ℝ, 0 ≤ t → (∀ g, P m g → ‖(lam g).toAdd‖ ≤ t) →
      ∀ g, P (m + 1) g → ‖(lam g).toAdd‖ ≤ (l:ℝ)⁻¹ * t := by
    intro m hm t ht hyp g hg
    have chain : ∀ k : ℕ, ∃ g', P (m + 1 + k) g' ∧
        ‖(lam g).toAdd‖ ≤ max ((l:ℝ)⁻¹ * t) ‖(lam g').toAdd‖ := by
      intro k
      induction k with
      | zero => exact ⟨g, by simpa using hg, le_max_right _ _⟩
      | succ k ih =>
        obtain ⟨g', hg', hle⟩ := ih
        have hg'2 : P (m + k + 1) g' := by
          rw [show m + k + 1 = m + 1 + k by omega]; exact hg'
        obtain ⟨h, g'', hh, hg'', rfl⟩ := hdec (m + k) (by omega) g' hg'2
        refine ⟨g'', ?_, hle.trans (max_le (le_max_left _ _) ((key h g'').trans
          (max_le_max ?_ le_rfl)))⟩
        · rw [show m + 1 + (k + 1) = m + k + 2 by omega]; exact hg''
        · exact mul_le_mul_of_nonneg_left (hyp h (hmono' m k h hh)) (inv_nonneg.2 hlpos.le)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hsmall ε hε
    obtain ⟨g', hg', hle⟩ := chain N
    have hsm := hN g' (hmono' N (m + 1) g' (by rw [show N + (m + 1) = m + 1 + N by omega]; exact hg'))
    exact hle.trans (max_le (le_add_of_nonneg_right hε.le)
      (hsm.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.2 hlpos.le) ht))))
  have levels : ∀ j : ℕ, ∀ g, P (m₀ + j) g → ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => intro g _; rw [pow_zero]; exact PadicInt.norm_le_one _
    | succ j ih =>
      intro g hg
      rw [pow_succ']
      exact step (m₀ + j) (by omega) _ (pow_nonneg (inv_nonneg.2 hlpos.le) _) ih g hg
  refine ⟨(l:ℝ) ^ m₀, fun m g hg => ?_⟩
  rcases le_or_gt m₀ m with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    calc ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := levels j g hg
      _ = (l:ℝ) ^ m₀ * ((l:ℝ)⁻¹) ^ (m₀ + j) := by
        rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, one_mul]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have e : (l:ℝ) ^ (m + j + 1) * ((l:ℝ)⁻¹) ^ m = (l:ℝ) ^ (j + 1) := by
      rw [show m + j + 1 = m + (j + 1) by omega, pow_add, mul_comm ((l:ℝ) ^ m), mul_assoc,
        ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, mul_one]
    rw [e]
    exact (PadicInt.norm_le_one _).trans (one_le_pow₀ (by exact_mod_cast hl.out.one_lt.le))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCount

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SelN (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (V : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  Coc1 c n V ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧
      Cob1 c n V (Ine (F := ℚ) B) z) ∧
    (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat V s 1 1 * x - x))

end GlobalTheory.Ord2.GwCount
end
end

