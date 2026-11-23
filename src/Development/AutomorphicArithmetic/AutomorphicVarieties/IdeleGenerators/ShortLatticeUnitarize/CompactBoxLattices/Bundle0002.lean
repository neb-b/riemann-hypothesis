module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkReps
section
open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.L2.Host

theorem UpperTheory.V.Sd.Wc.hkReps :
    UpperTheory.V.Sd.UopSum → UpperTheory.V.Sd.Wc.HkReps := by
  intro hU F _ _ w c
  classical
  haveI : Fintype (ResidueField (HeightOneSpectrum.adicCompletionIntegers F w)) := Fintype.ofFinite _
  let sec := Function.surjInv (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  have hsec : ∀ r, residue _ (sec r) = r :=
    Function.surjInv_eq (residue_surjective (R := HeightOneSpectrum.adicCompletionIntegers F w))
  let S := Finset.univ.image sec
  have hS : Set.BijOn (residue (HeightOneSpectrum.adicCompletionIntegers F w)) (↑S) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨r, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := hy
      rw [hsec, hsec] at hxy
      rw [hxy]
    · intro r _
      exact ⟨sec r, by simp [S], hsec r⟩
  let e : Fin S.card ≃ S := S.equivFin.symm
  let b : Fin S.card → GL (Fin 2) (HeightOneSpectrum.adicCompletion F w) :=
    fun i => aff ((atFin w) (unif w)) ↑((e i : HeightOneSpectrum.adicCompletionIntegers F w))
  have hsum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion F w)) V) (x : V),
      ∑ u ∈ S, (ρ (aff ((atFin w) (unif w)) ↑u)) x = ∑ i, (ρ (b i)) x := by
    intro V _ _ ρ x
    rw [← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp e (fun u : S => (ρ (aff ((atFin w) (unif w)) ↑(u : HeightOneSpectrum.adicCompletionIntegers F w))) x)).symm
  by_cases hc : c = 0
  · refine ⟨S.card + 1, Fin.cons ((Matrix.GeneralLinearGroup.scalar (Fin 2)) ((atFin w) (unif w)) * (aff ((atFin w) (unif w)) 0)⁻¹) b, fun h => absurd hc h, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_pos hc, Fin.sum_univ_succ, hsum, Fin.cons_zero, add_comm]
    simp only [Fin.cons_succ]
  · refine ⟨S.card, b, fun _ i => ⟨(e i : HeightOneSpectrum.adicCompletionIntegers F w), rfl⟩, ?_⟩
    intro V _ _ ρ x hx
    obtain ⟨h1, h2⟩ := hU F w V ρ c x hx
    refine ⟨h1, ?_⟩
    rw [h2 S hS, if_neg hc, add_zero, hsum]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.LocTwo
section
open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.ConjugateSelfDual

private theorem sq_two {O : Type} [CommRing O] (M : Matrix (Fin 2) (Fin 2) O) :
    M * M = (M 0 0 + M 1 1) • M - (M 0 0 * M 1 1 - M 0 1 * M 1 0) • (1 : Matrix (Fin 2) (Fin 2) O) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem pow_two_dim {O k : Type} [CommRing O] [CommRing k] (r : O →+* k) (M : Matrix (Fin 2) (Fin 2) O)
    (ht : r (M 0 0 + M 1 1) = 2) (hd : r (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 1) (n : ℕ) :
    ∃ U V : O, M ^ n = U • M + V • (1 : Matrix (Fin 2) (Fin 2) O) ∧ r U = n ∧ r V = 1 - n := by
  induction n with
  | zero => exact ⟨0, 1, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨U, V, h, hU, hV⟩ := ih
    refine ⟨U * (M 0 0 + M 1 1) + V, -(U * (M 0 0 * M 1 1 - M 0 1 * M 1 0)), ?_, ?_, ?_⟩
    · rw [pow_succ, h, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, sq_two M]
      module
    · rw [map_add (f := _), map_mul, ht, hU, hV]; push_cast; ring
    · rw [map_neg, map_mul, hd, hU]; push_cast; ring

private theorem field_two {k : Type} [Field k] (hk : Nat.card k = 2) :
    (∀ x : k, x ≠ 0 → x = 1) ∧ (2 : k) = 0 := by
  have h1 : ∀ x : k, x ≠ 0 → x = 1 := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
    intro x hx
    rw [hy x hx, hy 1 one_ne_zero]
  refine ⟨h1, ?_⟩
  by_contra h
  have := h1 2 h
  have h2 : (1 : k) = 0 := by linear_combination this
  exact one_ne_zero h2

private theorem gen {O K : Type} [CommRing O] [IsLocalRing O] [Field K] (φ : O →+* K)
    (hk : Nat.card (ResidueField O) = 2) (h : GL (Fin 2) O)
    (hc : residue O (h 1 0) = 0) (hd : residue O (h 1 1) = 1) (n : ℕ) (hn : Odd n)
    (hz : (Matrix.GeneralLinearGroup.map φ h) ^ n ∈ Subgroup.center (GL (Fin 2) K)) :
    Matrix.GeneralLinearGroup.map φ h ∈ Subgroup.center (GL (Fin 2) K) := by
  obtain ⟨h1, h2⟩ := field_two hk
  have hu := (Matrix.GeneralLinearGroup.det h).isUnit
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hu
  have hdet : residue O (h 0 0 * h 1 1 - h 0 1 * h 1 0) = 1 := h1 _ (hu.map (residue O)).ne_zero
  have ha : residue O (h 0 0) = 1 := by
    rw [map_sub, map_mul, map_mul, hc, hd] at hdet
    simpa using hdet
  obtain ⟨U, V, hp, hU, -⟩ := pow_two_dim (residue O) (h : Matrix (Fin 2) (Fin 2) O)
    (by rw [map_add (f := _), ha, hd]; norm_num) hdet n
  have hUu : IsUnit U := by
    by_contra hU'
    have h0 : residue O U = 0 := (residue_eq_zero_iff U).2 hU'
    obtain ⟨m, rfl⟩ := hn
    rw [h0] at hU
    push_cast at hU
    rw [h2] at hU
    simp at hU
  have hU0 : φ U ≠ 0 := (hUu.map φ).ne_zero
  set k := Matrix.GeneralLinearGroup.map φ h with hkdef
  have hkp : ((k ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      φ U • (k : Matrix (Fin 2) (Fin 2) K) + φ V • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hkdef, ← map_pow]
    change ((h ^ n : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O).map φ =
      φ U • (h : Matrix (Fin 2) (Fin 2) O).map φ + φ V • (1 : Matrix (Fin 2) (Fin 2) K)
    rw [Units.val_pow_eq_pow_val, hp]
    ext i j
    simp [Matrix.one_apply, apply_ite φ]
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have hg := congrArg Units.val (hz g)
  rw [Units.val_mul, Units.val_mul, hkp, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, mul_one, one_mul, add_left_inj] at hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact smul_right_injective _ hU0 hg

theorem UpperTheory.V.Sd.Wc.locTwo :
    UpperTheory.V.Sd.Wc.LocTwo := by
  intro F _ _ u c hc hN k hk n hn hz
  obtain ⟨h, hh, rfl⟩ := hk
  have hle : maximalIdeal (u.adicCompletionIntegers F) ^ c ≤ maximalIdeal _ := Ideal.pow_le_self hc
  refine gen _ ?_ h ?_ ?_ n hn hz
  · rw [Formalism.UG.P.tjcosets_card_residue, ← hN]
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · have h0 := congrFun hh 0
    rw [residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  · have h0 := congrFun hh 1
    rw [← map_one (residue (u.adicCompletionIntegers F)), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    apply hle
    rw [← Ideal.Quotient.eq, map_one]
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private noncomputable def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

private theorem isOpen_mP (w : Pl F) (c : ℕ) : IsOpen (mP w c : Set (w.adicCompletion F)) := by
  have h0 : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≠ ⊥ :=
    pow_ne_zero c (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have ha1 : (a : w.adicCompletion F) ≠ 0 := fun e => ha0 (Subtype.ext e)
  have ho : IsOpen ((fun x : w.adicCompletion F => (a : w.adicCompletion F)⁻¹ * x) ⁻¹'
      (w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  refine ⟨a * ⟨_, hx⟩, Ideal.mul_mem_right _ _ ha, ?_⟩
  change (a : w.adicCompletion F) * ((a : w.adicCompletion F)⁻¹ * x) = x
  rw [mul_inv_cancel_left₀ ha1]

private theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

private theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

private theorem mem_Oh {x : Af F} :
    x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  rw [← mem_Ohat]; simp [Ohat, Subring.mem_iInf]

private theorem mem_Kc {c : Pl F → ℕ} {g : GF F} :
    g ∈ Kc c ↔ g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 ∧
      ∀ w, c w ≠ 0 → pLoc F w (g 1 0) ∈ mP w (c w) ∧ pLoc F w (g 1 1) - 1 ∈ mP w (c w) := by
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv,
    GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, mem_Oh]
  constructor
  · exact fun h => ⟨⟨fun a b w => (h w).1 a b, fun a b w => (h w).2.1 a b⟩, fun w _ => (h w).2.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ w
    refine ⟨fun a b => h1 a b w, fun a b => h2 a b w, ?_⟩
    by_cases hw : c w = 0
    · rw [hw]
      exact ⟨mem_mP_zero (h1 1 0 w), mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩
    · exact h3 w hw

private theorem isOpen_Kc {c : Pl F → ℕ} (hc : {w | c w ≠ 0}.Finite) : IsOpen (Kc c : Set (GF F)) := by
  have e : (Kc c : Set (GF F)) = (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F 2 : Set (GF F)) ∩
      ⋂ w ∈ {w | c w ≠ 0}, ((fun g : GF F => pLoc F w (g 1 0)) ⁻¹' mP w (c w) ∩
        (fun g : GF F => pLoc F w (g 1 1) - 1) ⁻¹' mP w (c w)) := by
    ext g
    simp only [SetLike.mem_coe, mem_Kc, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  have ct : ∀ w a b, Continuous fun g : GF F => pLoc F w (g a b) := fun w a b =>
    (show Continuous (pLoc F w) from RestrictedProduct.continuous_eval w).comp
      (Continuous.matrix_elem Units.continuous_val a b)
  rw [e]
  exact (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL F 2).inter (hc.isOpen_biInter fun w _ =>
    ((isOpen_mP w _).preimage (ct w 1 0)).inter ((isOpen_mP w _).preimage ((ct w 1 1).sub continuous_const)))

private theorem range_zc : ((zc F).range : Set (GF F)) =
    {g : GF F | g 0 1 = 0} ∩ {g : GF F | g 1 0 = 0} ∩ {g : GF F | g 0 0 = g 1 1} := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    simp [zc]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    have hm : g 0 0 * (g⁻¹ : GF F) 0 0 = 1 := by
      have := congrFun (congrFun g.mul_inv 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, h1, zero_mul, add_zero] at this
      exact this
    refine ⟨Units.mkOfMulEqOne _ _ hm, Units.ext (Matrix.ext fun i j => ?_)⟩
    fin_cases i <;> fin_cases j <;> simp [zc, h1, h2, h3]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.kcTop :
    UpperTheory.V.Sd.Wc.KcTop := by
  intro F _ _
  have ct : ∀ a b, Continuous fun g : GF F => g a b := fun a b => Continuous.matrix_elem Units.continuous_val a b
  refine ⟨fun c hc => ⟨isOpen_Kc hc, ?_⟩, fun U hU => ?_, fun z => ?_, ?_, ?_, fun c w k hk => ?_⟩
  · exact (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F 2).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_Kc hc)) fun g hg => (mem_Kc.1 hg).1
  · obtain ⟨H, -, hH⟩ := (GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one F 2).mem_iff.1 hU
    exact ⟨H.toSubgroup, H.isOpen, hH⟩
  · refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact ((Matrix.scalar_commute (z : Af F) (fun _ => Commute.all _ _) g.val).eq).symm
  · rw [range_zc]
    exact ((isClosed_eq (ct 0 1) continuous_const).inter (isClosed_eq (ct 1 0) continuous_const)).inter
      (isClosed_eq (ct 0 0) (ct 1 1))
  · refine Continuous.units_map _ ?_
    exact (continuous_pi fun _ => continuous_id : Continuous fun x : Af F => fun _ : Fin 2 => x).matrix_diagonal
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
    by_cases h : v = w
    · subst h; rwa [pLoc_locGL]
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
section
noncomputable section

open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Sd.Wc

private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring

private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)

end UpperTheory.V.Sd.Wc

open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2 :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end

