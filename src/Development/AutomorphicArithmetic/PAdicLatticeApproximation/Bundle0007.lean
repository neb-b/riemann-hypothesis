module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle0005
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDenominatorOfLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma exists_den_finset {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ s, ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a :=
  _root_.UpperTheory.Reformulated.B.Qh61.exists_den_finset D s

private lemma exists_den_closure {p : ℕ} [Fact p.Prime] (D : Datum p) (s : Finset (VQ D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ AddSubgroup.closure (s : Set (VQ D)),
      ∃ a : D.La, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  obtain ⟨k, hk, hs⟩ := exists_den_finset D s
  refine ⟨k, hk, fun x hx => ?_⟩
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [smul_add, ha, hb, TensorProduct.tmul_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨-a, by rw [smul_neg, ha, TensorProduct.tmul_neg]⟩

theorem UpperTheory.exists_denominator_of_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D X
  obtain ⟨-, s, -, hmem⟩ := X.hM
  obtain ⟨k, hk, hkc⟩ := exists_den_closure D s
  obtain ⟨j, hj, -, hjS⟩ := GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem p D X.S
  refine ⟨k * j, Nat.mul_pos hk hj, fun w hw => ?_⟩
  obtain ⟨m, hm, hc⟩ := (hmem w).1 hw.1
  obtain ⟨a₁, ha₁⟩ := hkc _ hc
  have hST : X.S (X.r w) = (1 : AfP p) ⊗ₜ[ℚ] w := by
    have h := congrArg (fun f => f ((1 : AfP p) ⊗ₜ[ℚ] w)) X.ST
    simpa [UpperTheory.Gal.W2.Wit.Sys.r_apply] using h
  have hin : (1 : AfP p) ⊗ₜ[ℚ] (j • w) ∈ LaHat D := by
    have h := hjS _ hw.2
    rw [hST] at h
    rwa [TensorProduct.tmul_smul]
  obtain ⟨r, a₂, ha₂⟩ := UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice p D (j • w) hin
  have hcop : IsCoprime (m : ℤ) ((p ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right r hm)
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(u * j) • a₁ + (v * k) • a₂, ?_⟩
  have e₁ : ((k : ℤ) * m) • w = (1 : ℚ) ⊗ₜ[ℤ] a₁ := by
    rw [← ha₁, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  have e₂ : (((p ^ r : ℕ) : ℤ) * j) • w = (1 : ℚ) ⊗ₜ[ℤ] a₂ := by
    rw [← ha₂, smul_smul, ← Nat.cast_mul, natCast_zsmul]
  rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← e₁, ← e₂,
    smul_smul, smul_smul, ← add_smul, ← natCast_zsmul]
  congr 1
  push_cast at huv ⊢
  linear_combination (-(k : ℤ) * j) * huv
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsIntBilinFormOfScaledForm
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_int_bilinForm_of_scaled_form :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D),
      ∃ E : LinearMap.BilinForm ℤ X.lat,
        ∀ u w : X.lat, (E u w : ℚ) = X.s * X.B (u : VQ D) (w : VQ D) := by
  intro p _ D X
  have h : ∀ u w : X.lat, ((X.s * X.B (u : VQ D) (w : VQ D)).num : ℚ)
      = X.s * X.B (u : VQ D) (w : VQ D) := fun u w =>
    Rat.intCast_num_of_den_eq_one (UpperTheory.scaled_form_den_eq_one_on_lattice p D X u w u.2 w.2)
  refine ⟨LinearMap.mk₂ ℤ (fun u w : X.lat => (X.s * X.B (u : VQ D) (w : VQ D)).num)
    ?_ ?_ ?_ ?_, ?_⟩
  · intro u u' w
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add X.B, LinearMap.add_apply, mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower X.B, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  · intro u w w'
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, h, h, h, AddSubgroup.coe_add, map_add (X.B (u : VQ D)), mul_add]
  · intro c u w
    apply Int.cast_injective (α := ℚ)
    rw [smul_eq_mul, Int.cast_mul, h, h, AddSubgroup.coe_zsmul,
      LinearMap.map_smul_of_tower (X.B (u : VQ D)), zsmul_eq_mul]
    ring
  · intro u w
    rw [LinearMap.mk₂_apply]
    exact h u w
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsLatticeLiftCongrModCoprime
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_lattice_lift_congr_mod_coprime :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ f : ℕ → D.La →+ X.lat, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a : D.La, ∃ e ∈ LaHat D, X.r (f n a : VQ D) = inAf D a + n • e := by
  intro p _ D X
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a : D.La,
      ∃ u ∈ X.lat, ∃ e ∈ LaHat D, X.r u = inAf D a + n • e :=
    fun n hn hc a => UpperTheory.exists_lattice_approx_mod_n_completedLattice p D X n hn hc a
  let g : ℕ → Module.Free.ChooseBasisIndex ℤ D.La → X.lat := fun n i =>
    if h : 0 < n ∧ n.Coprime p then
      ⟨(key n h.1 h.2 (b i)).choose, (key n h.1 h.2 (b i)).choose_spec.1⟩
    else 0
  refine ⟨fun n => (b.constr ℤ (g n)).toAddMonoidHom, ?_⟩
  intro n hn hc a
  let φ : D.La →+ AfP p ⊗[ℚ] VQ D :=
    ((X.r.toAddMonoidHom.comp X.lat.subtype).comp (b.constr ℤ (g n)).toAddMonoidHom)
      - AdelicSim.inAfHom D
  let H : AddSubgroup (AfP p ⊗[ℚ] VQ D) := (LaHat D).map (nsmulAddMonoidHom n)
  have hb : ∀ i, b i ∈ H.comap φ := by
    intro i
    obtain ⟨e, he, heq⟩ := (key n hn hc (b i)).choose_spec.2
    refine AddSubgroup.mem_comap.mpr (AddSubgroup.mem_map.mpr ⟨e, he, ?_⟩)
    have hg : g n i = ⟨(key n hn hc (b i)).choose, (key n hn hc (b i)).choose_spec.1⟩ :=
      dif_pos ⟨hn, hc⟩
    simp only [φ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      Module.Basis.constr_basis, hg, AddSubgroup.coe_subtype, nsmulAddMonoidHom_apply]
    rw [heq, ← AdelicSim.inAf_eq]
    abel
  have htop : H.comap φ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [b.span_eq]; trivial
    rw [Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hb i) hx
  have ha : a ∈ H.comap φ := htop ▸ AddSubgroup.mem_top a
  obtain ⟨e, he, heq⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_comap.mp ha)
  refine ⟨e, he, ?_⟩
  simp only [φ, nsmulAddMonoidHom_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, AddSubgroup.coe_subtype] at heq
  rw [AdelicSim.inAf_eq, heq]
  abel
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormCongrModNOfUnitCongr
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.scaled_form_congr_mod_n_of_unit_congr :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ) (ν : ℤ) (b : AfP p) (u u' : VQ D) (a a' : D.La) (e e' : AfP p ⊗[ℚ] VQ D), 0 < n → n.Coprime p → IsIntAf b → (X.ε : AfP p) = (ν : AfP p) + (n : AfP p) * b → u ∈ X.lat → u' ∈ X.lat → e ∈ LaHat D → e' ∈ LaHat D → X.r u = inAf D a + n • e → X.r u' = inAf D a' + n • e' → ∃ z : ℤ, X.s * X.B u u' = (ν : ℚ) * (D.EF a a' : ℤ) + (n : ℚ) * z := by
  intro p _ D X n ν b u u' a a' e e' hn hc hb hε hu hu' he he' hr hr'
  have hden := UpperTheory.scaled_form_den_eq_one_on_lattice p D X u u' hu hu'
  have hform : algebraMap ℚ (AfP p) (X.s * X.B u u') =
      (X.ε : AfP p) * MultScale.EFA D (X.r u) (X.r u') := X.form u u'
  generalize X.s * X.B u u' = q at hden hform ⊢
  have hqz : ((q.num : ℤ) : ℚ) = q := Rat.coe_int_num_of_den_eq_one hden
  have ha := MultScale.inAf_mem D a
  have ha' := MultScale.inAf_mem D a'
  obtain ⟨y, hy, hexp⟩ : ∃ y : AfP p, IsIntAf y ∧
      MultScale.EFA D (inAf D a + n • e) (inAf D a' + n • e') =
        ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y := by
    refine ⟨MultScale.EFA D (inAf D a) e' + MultScale.EFA D e (inAf D a') +
      (n : AfP p) * MultScale.EFA D e e', ?_, ?_⟩
    · exact MultScale.isIntAf_add (MultScale.isIntAf_add (MultScale.isIntAf_EFA D ha he')
        (MultScale.isIntAf_EFA D he ha')) (MultScale.isIntAf_mul
          (by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)) (MultScale.isIntAf_EFA D he he'))
    · simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
        MultScale.EFA_inAf]
      ring
  rw [hr, hr', hexp, hε] at hform
  have hE := MultScale.isIntAf_intCast (p := p) (D.EF a a')
  have hN : IsIntAf (n : AfP p) := by simpa using MultScale.isIntAf_intCast (p := p) (n : ℤ)
  have hy' : IsIntAf ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) :=
    MultScale.isIntAf_add (MultScale.isIntAf_mul (MultScale.isIntAf_intCast ν) hy)
      (MultScale.isIntAf_mul hb (MultScale.isIntAf_add hE (MultScale.isIntAf_mul hN hy)))
  have hc' : algebraMap ℚ (AfP p) (((q.num - ν * (D.EF a a' : ℤ) : ℤ)) : ℚ) =
      (n : AfP p) * ((ν : AfP p) * y + b * (((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * y)) := by
    have h1 : algebraMap ℚ (AfP p) ((q.num : ℤ) : ℚ) = algebraMap ℚ (AfP p) q := by rw [hqz]
    rw [map_intCast] at h1 ⊢
    push_cast
    rw [h1, hform]
    ring
  obtain ⟨k, hk⟩ := IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _ _ hy' hc'
  refine ⟨k, ?_⟩
  have hk' : ((q.num : ℤ) : ℚ) - (ν : ℚ) * (D.EF a a' : ℤ) = (n : ℚ) * k := by exact_mod_cast hk
  rw [← hqz]
  linarith
end

