module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
section
noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] [NumberField E]

theorem int_nat (m : ℕ) : IsIntegral ℤ (m : E) := by
  have h := isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ))
  simpa using h

theorem int_sigma (σ : E →+* E) {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (σ a) := ha.map σ.toIntAlgHom

theorem mat_den {M : ℕ} (A : Matrix (Fin M) (Fin M) E) : ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : E) * A i j) := by
  have hex : ∀ a : E, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
    intro a
    have halg : IsAlgebraic ℤ a := by
      first
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff (R := ℤ) (K := ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact Algebra.IsAlgebraic.isAlgebraic a
    obtain ⟨y, hy0, hy⟩ : ∃ y ≠ (0 : ℤ), IsIntegral ℤ (y • a) := by
      first
      | exact halg.exists_integral_multiple
      | exact exists_integral_multiple halg
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
    have hcast : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
    rcases (show ((y.natAbs : ℕ) : ℤ) = y ∨ ((y.natAbs : ℕ) : ℤ) = -y by omega) with h | h
    · rw [hcast, h, ← zsmul_eq_mul]
      exact hy
    · rw [hcast, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  choose d hd0 hd using fun p : Fin M × Fin M => hex (A p.1 p.2)
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd0 p, fun i j => ?_⟩
  have hsplit : (∏ p, d p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), d p) * d (i, j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  rw [hsplit, Nat.cast_mul, mul_assoc]
  exact (int_nat _).mul (hd (i, j))

theorem lattice_classes_finite_refinement : LatFin := by
  intro E _ _ σ M J D T c0 hσ hpos hD hT hc0
  classical
  set J' : Matrix (Fin M) (Fin M) E := (D : E) • J with hJ'
  have hpos' : ∀ τ : E →+* ℂ, (J'.map τ).PosDef := by
    intro τ
    have : J'.map τ = (D : ℂ) • J.map τ := by
      ext i j
      simp [hJ', map_natCast]
    rw [this]
    exact (hpos τ).smul (by exact_mod_cast hD)
  obtain ⟨SE, hSEf, hSE⟩ := hermitian_lattice_finite E M σ J' T hσ hpos' hT
  let Sub : Submodule (𝓞 E) (Fin M → E) → Set (Set (Fin M → E)) := fun N₀ =>
    {s | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N₀, (c0 : E) • x ∈ s) ∧ s ⊆ N₀}
  refine ⟨⋃ N₀ ∈ {N₀ | N₀ ∈ SE ∧ N₀.FG}, Sub N₀,
    Set.Finite.biUnion (hSEf.subset (by exact fun N₀ h => h.1)) fun N₀ h => sub_finite N₀ h.2 c0 hc0, ?_⟩
  intro Λ h1 h2 h3 h4
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'

  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hpos τ).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨d, hd, hdJ⟩ := mat_den J⁻¹
  set N : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Λ : Set (Fin M → E)) with hNdef
  have smul_coe : ∀ (a : 𝓞 E) (y : Fin M → E), a • y = (a : E) • y := fun a y => rfl

  have hI1 : ∀ x ∈ Λ, ∀ y ∈ N, IsIntegral ℤ ((D : E) * herm σ J x y) := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h3 x hx y hy
    | zero => rw [herm_zero_right, mul_zero]; exact isIntegral_zero
    | add y z _ _ h1 h2 => rw [herm_add_right, mul_add]; exact h1.add h2
    | smul a y _ h1 =>
      rw [smul_coe, herm_smul_right, mul_left_comm]
      exact a.isIntegral_coe.mul h1
  have hI : ∀ x ∈ N, ∀ y ∈ N, IsIntegral ℤ (herm σ J' x y) := by
    intro x hx y hy
    rw [hJ', herm_scale]
    induction hx using Submodule.span_induction with
    | mem x hx => exact hI1 x hx y hy
    | zero => rw [herm_zero_left, mul_zero]; exact isIntegral_zero
    | add x z _ _ h1 h2 => rw [herm_add_left, mul_add]; exact h1.add h2
    | smul a x _ h1 =>
      rw [smul_coe, herm_smul_left, mul_left_comm]
      exact (int_sigma σ a.isIntegral_coe).mul h1

  have hDual : ∀ y : Fin M → E, (∀ x ∈ N, IsIntegral ℤ (herm σ J' x y)) → (T : E) • y ∈ N := by
    intro y hy
    refine Submodule.subset_span (h4 y fun x hx => ?_)
    have := hy x (Submodule.subset_span hx)
    rwa [hJ', herm_scale] at this

  obtain ⟨k, hk, hkΛ⟩ := h2
  have hsing : ∀ i, (Pi.single i (k : E) : Fin M → E) ∈ Λ := by
    intro i
    have := hkΛ i 1 isIntegral_one
    rwa [mul_one] at this
  have hNfg : N.FG := by
    refine fg_of_den N (d * D * k) (Nat.mul_pos (Nat.mul_pos hd hD) hk) fun y hy j => ?_
    have hJy : ∀ i, IsIntegral ℤ ((D : E) * (k : E) * (J.mulVec y) i) := by
      intro i
      have := hI1 _ (hsing i) y hy
      rwa [herm_single_left, ← mul_assoc] at this
    obtain ⟨w, hw⟩ : ∃ w, w = J.mulVec y := ⟨_, rfl⟩
    have hy' : y = J⁻¹.mulVec w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hJdet), Matrix.one_mulVec]
    rw [← hw] at hJy
    have : ((d * D * k : ℕ) : E) * y j = ∑ i, ((d : E) * J⁻¹ j i) * ((D : E) * (k : E) * w i) := by
      conv_lhs => rw [hy']
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [this]
    exact IsIntegral.sum _ fun i _ => (hdJ j i).mul (hJy i)
  have hNspan : Submodule.span E (N : Set (Fin M → E)) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hkE : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
    have hv : v = ∑ j, (v j / (k : E)) • (Pi.single j (k : E) : Fin M → E) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Pi.single_smul]
      congr 1
      rw [smul_eq_mul, div_mul_cancel₀ _ hkE]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span (hsing j)))
  have hAdm : admitted σ J' T N := ⟨⟨hNfg, hNspan⟩, hI, hDual⟩
  obtain ⟨N₀, hN₀, g, hg, hgN⟩ := hSE N hAdm

  have hJ'det : J'.det ≠ 0 := by
    rw [hJ', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hDE) hJdet
  have hgdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hJ'det this.symm
  have hgU : PI.UJClassFin.cT σ g * J * g = J := by
    have e1 : (g.map σ)ᵀ * J' * g = (D : E) • (PI.UJClassFin.cT σ g * J * g) := by
      rw [hJ', Matrix.mul_smul, Matrix.smul_mul]
      rfl
    have := hg
    unfold IsUJ at this
    rw [e1] at this
    exact smul_right_injective _ hDE this
  let G : GL (Fin M) E := Matrix.nonsingInvUnit g (Ne.isUnit hgdet)
  have hGg : ((G : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = g := rfl
  have hGU : G ∈ PI.UJClassFin.UJ σ J := by
    show PI.UJClassFin.cT σ (G : Matrix (Fin M) (Fin M) E) * J * (G : Matrix (Fin M) (Fin M) E) = J
    rw [hGg]; exact hgU
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hgdet)
  have hig : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hgdet)

  have hN₀eq : (N₀ : Set (Fin M → E)) = (fun x => g⁻¹.mulVec x) '' (N : Set (Fin M → E)) := by
    rw [← hgN, Set.image_image]
    simp only [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec, Set.image_id']
  have hN₀fg : N₀.FG := by
    have : N₀ = N.map ((Matrix.mulVecLin g⁻¹).restrictScalars (𝓞 E)) := by
      apply SetLike.coe_injective
      rw [hN₀eq, Submodule.map_coe]
      rfl
    rw [this]
    exact hNfg.map _

  have hc0N : ∀ y ∈ N, (c0 : E) • y ∈ Λ := by
    let Nc : Submodule (𝓞 E) (Fin M → E) :=
      { carrier := {y | ∀ a : 𝓞 E, (c0 : E) • ((a : E) • y) ∈ Λ}
        add_mem' := fun {y z} hy hz a => by rw [smul_add, smul_add]; exact Λ.add_mem (hy a) (hz a)
        zero_mem' := fun a => by rw [smul_zero, smul_zero]; exact Λ.zero_mem
        smul_mem' := fun b y hy a => by
          show (c0 : E) • ((a : E) • (b • y)) ∈ Λ
          have e : (a : E) • (b • y) = ((a * b : 𝓞 E) : E) • y := by
            rw [smul_coe b y, smul_smul]
            rfl
          rw [e]
          exact hy (a * b) }
    have hle : N ≤ Nc := by
      rw [hNdef, Submodule.span_le]
      intro x hx a
      rw [smul_smul]
      exact h1 x hx _ a.isIntegral_coe
    intro y hy
    have := hle hy 1
    rwa [show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul] at this
  let s : Set (Fin M → E) := (fun x => g⁻¹.mulVec x) '' (Λ : Set (Fin M → E))
  have hs : s ∈ Sub N₀ := by
    refine ⟨⟨Λ.map (Matrix.mulVecLin g⁻¹).toAddMonoidHom, by rw [AddSubgroup.coe_map]; rfl⟩, ?_, ?_⟩
    · intro x hx
      have hgx : g.mulVec x ∈ N := by rw [← SetLike.mem_coe, ← hgN]; exact ⟨x, hx, rfl⟩
      refine ⟨(c0 : E) • g.mulVec x, hc0N _ hgx, ?_⟩
      show g⁻¹.mulVec ((c0 : E) • g.mulVec x) = (c0 : E) • x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
    · rintro _ ⟨x, hx, rfl⟩
      show g⁻¹.mulVec x ∈ (N₀ : Set (Fin M → E))
      rw [hN₀eq]
      exact Set.mem_image_of_mem _ (Submodule.subset_span hx)
  refine ⟨s, Set.mem_biUnion ⟨hN₀, hN₀fg⟩ hs, ⟨G, hGU⟩, ?_⟩
  show (Λ : Set (Fin M → E)) = (fun x => g.mulVec x) '' s
  rw [Set.image_image]
  simp only [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec, Set.image_id']

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense
section
noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem single_tmul (l : Fin M) (a : Af F) (t : E) :
    Pi.single l (a ⊗ₜ[F] t) = fun i => a ⊗ₜ[F] ((Pi.single l t : Fin M → E) i) := by
  funext i
  by_cases h : i = l
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem nsmul_tmul_F (N : ℕ) (a : Af F) (e : E) : N • (a ⊗ₜ[F] e) = a ⊗ₜ[F] ((N : F) • e) := by
  first
  | (rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul])
  | (induction N with
      | zero => simp
      | succ n ih => simp [succ_nsmul, ih, add_smul, TensorProduct.tmul_add])

theorem mulVec_single' (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (j : Fin M) (x : Af F ⊗[F] E) :
    g.mulVec (Pi.single j x) = fun l => g l j * x := by
  funext l
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem latHat_smul (L : Set (Fin M → E)) {a : Af F} (ha : a ∈ intAf F) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : (a ⊗ₜ[F] (1 : E)) • y ∈ latHat F E L := by
  unfold latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    have hmul : a * a' ∈ intAf F := by
      unfold intAf at ha ha' ⊢
      intro v
      rw [map_mul]
      exact mul_mem (ha v) (ha' v)
    refine ⟨a * a', hmul, x, hx, ?_⟩
    funext i
    simp [Pi.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem single_mem (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {p : Af F ⊗[F] E} (hp : p ∈ Oh F E) (l : Fin M) : Pi.single l (k • p) ∈ latHat F E L := by
  let S' : AddSubgroup (Af F ⊗[F] E) :=
    { carrier := {q | Pi.single l (k • q) ∈ latHat F E L}
      add_mem' := fun {a b} ha hb => by
        show Pi.single l (k • (a + b)) ∈ latHat F E L
        rw [smul_add, Pi.single_add]
        exact add_mem ha hb
      zero_mem' := by
        show Pi.single l (k • (0 : Af F ⊗[F] E)) ∈ latHat F E L
        rw [smul_zero, Pi.single_zero]
        exact zero_mem _
      neg_mem' := fun {a} ha => by
        show Pi.single l (k • (-a)) ∈ latHat F E L
        rw [smul_neg, Pi.single_neg]
        exact neg_mem ha }
  have hsub : {r : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e} ⊆
      (S' : Set _) := by
    rintro r ⟨a, ha, e, he, rfl⟩
    show Pi.single l (k • (a ⊗ₜ[F] e)) ∈ latHat F E L
    rw [nsmul_tmul_F, single_tmul]
    unfold latHat
    exact AddSubgroup.subset_closure ⟨a, ha, Pi.single l ((k : F) • e), hk l e he, rfl⟩
  exact (AddSubgroup.closure_le S').mpr hsub hp

theorem rational_points_dense : RatDense := by
  intro F E _ _ _ _ _ σ M J L _h4 h5 h y
  classical
  obtain ⟨k, hk, hkL⟩ := low_nat L h5
  set g' := finMat σ J h⁻¹ with hg'
  have hden : ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g' l j ∈ Oh F E := by
    choose mf hmf hmO using fun p : Fin M × Fin M => den (g' p.1 p.2)
    refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _
  obtain ⟨m, hm, hmO⟩ := hden
  have K1 : ∀ o ∈ Oh F E, ∀ j, g'.mulVec (Pi.single j ((k * m) • o)) ∈ latHat F E L := by
    intro o ho j
    rw [mulVec_single']
    have : (fun l => g' l j * ((k * m) • o)) = ∑ l, Pi.single l (k • ((m • g' l j) * o)) := by
      rw [Finset.univ_sum_single (fun l => k • ((m • g' l j) * o))]
      funext l
      rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [this]
    exact AddSubgroup.sum_mem _ (fun l _ => single_mem L hkL (Oh_mul (hmO l j) ho) l)
  have SL : ∀ p ∈ Oh F E, ∀ j, Pi.single j ((k * m) • p) ∈ latHat F E (abelian₂ σ J L h) := by
    intro p hp j
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨a, ha, e, he, rfl⟩ := hp
      rw [nsmul_tmul_F, single_tmul]
      refine AddSubgroup.subset_closure ⟨a, ha, _, ?_, rfl⟩
      show g'.mulVec (vinc (Pi.single j (((k * m : ℕ) : F) • e))) ∈ latHat F E L
      have hv : vinc (F := F) (Pi.single j (((k * m : ℕ) : F) • e)) = Pi.single j ((k * m) • ((1 : Af F) ⊗ₜ[F] e)) := by
        rw [nsmul_tmul_F, single_tmul]
        rfl
      rw [hv]
      exact K1 _ (tmul_mem_Oh intAf_one he) j
    | zero => rw [smul_zero, Pi.single_zero]; exact zero_mem _
    | add p q _ _ h1 h2 => rw [smul_add, Pi.single_add]; exact add_mem h1 h2
    | neg p _ h1 => rw [smul_neg, Pi.single_neg]; exact neg_mem h1
  constructor
  · intro hy
    choose e o ho hyo using fun j => approx (F := F) (k * m) (Nat.mul_pos hk hm) (y j)
    have hyw : y = vinc (F := F) e + ∑ j, Pi.single j ((k * m) • o j) := by
      rw [Finset.univ_sum_single (fun j => (k * m) • o j)]
      funext j
      exact hyo j
    have hwsum : g'.mulVec (∑ j, Pi.single j ((k * m) • o j)) ∈ latHat F E L := by
      rw [Matrix.mulVec_sum]
      exact AddSubgroup.sum_mem _ (fun j _ => K1 _ (ho j) j)
    have he : e ∈ abelian₂ σ J L h := by
      show g'.mulVec (vinc e) ∈ latHat F E L
      have : vinc (F := F) e = y - ∑ j, Pi.single j ((k * m) • o j) := by
        conv_rhs => rw [hyw]
        abel
      rw [this, Matrix.mulVec_sub]
      exact sub_mem hy hwsum
    rw [hyw]
    refine add_mem (AddSubgroup.subset_closure ⟨1, intAf_one, e, he, rfl⟩) ?_
    exact AddSubgroup.sum_mem _ (fun j _ => SL _ (ho j) j)
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hx' : g'.mulVec (vinc x) ∈ latHat F E L := hx
      have : (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F := F) x := by
        funext i
        simp [vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, Matrix.mulVec_smul]
      exact latHat_smul L ha hx'
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

