module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ScalarComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.StabG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbitImp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DOrb
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.dOrb : UpperTheory.V.Z.Sym.Loc.DOrb := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j h1 h2
  haveI := L.frac
  obtain ⟨φ, p1, p2, p3, p4⟩ := dIso O K Δ L
  obtain ⟨j', q1, q2, q3⟩ := p4 τ γ j h1 h2
  have sc : ∀ z : Kˣ, IsScal z (φ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := fun z => (p2 _ _).2 (by simp)
  have hZ : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := fun g => by
    constructor
    · intro h
      refine (sup_le ?_ ?_ : ZD Δ ⊔ KD Δ O ≤ (ZK O K).comap φ.toMonoidHom) h
      · rintro s ⟨z, hz⟩
        exact Subgroup.mem_sup_left ⟨z, ((p2 z s).1 (congrArg Units.val hz).symm).symm⟩
      · exact fun k hk => Subgroup.mem_sup_right ((p1 k).2 hk)
    · intro h
      obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [← φ.symm_apply_apply g, e, map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨z, Units.ext (sc z).symm⟩) (Subgroup.mem_sup_right ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩)))
  have hf : ∀ χ : Kˣ →* ℂˣ, Unr O χ → ∀ g, fZD O χ g = fZK O χ (φ g) := fun χ hχ g => by
    by_cases h : φ g ∈ ZK O K
    · obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [e, (fzkLaw O K Δ L χ hχ).2 z _ ⟨k, rfl⟩, ← φ.symm_apply_apply g, e, map_mul]
      exact (fzdLaw O K Δ L χ hχ).2 z _ _ (sc z) ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩))
    · rw [(fzkLaw O K Δ L χ hχ).1 _ h, (fzdLaw O K Δ L χ hχ).1 _ fun h' => h ((hZ g).1 h')]
  have main : ∀ (χ : Kˣ →* ℂˣ), Unr O χ → ∀ (f : DX Δ → ℂ) (z : (Etau K τ)ˣ), (∀ y, f (y⁻¹ * j z * y) = fZK O χ (φ (y⁻¹ * j z * y))) →
      orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) f (j z) = gOrb O j' χ z := fun χ hχ f z H => by
    refine orb_congr j (jU j') _ _ _ _ _ _ _ _ _ φ.toEquiv (fun t y => ?_) (fun y y' => ?_) (fun y => ?_) (fun y y' h => ?_) fun t => ?_
    · simp [q3]
    · simp [hZ]
    · change f (y⁻¹ * j z * y) = fZK O χ ((φ y)⁻¹ * jU j' z * φ y)
      rw [H, map_mul, map_mul, map_inv, q3]
    · change f (y⁻¹ * j z * y) = f (y'⁻¹ * j z * y')
      rw [H, H, ← fZK_conj L hχ ((hZ _).1 h)]; simp [mul_assoc]
    · change _ * j z * j t = j z
      rw [mul_assoc, ← map_mul, mul_comm z, map_mul, inv_mul_cancel_left]
  refine ⟨j', q2, fun a ha => ?_, fun χ hχ z => main χ hχ _ z fun y => hf χ hχ _⟩
  have ea : j a = γ := φ.injective (by rw [q3]; exact Units.ext (by rw [← q1, ← ha]; rfl))
  rw [dS, ← ea]
  refine main 1 (fun _ => rfl) _ a fun y => ?_
  have F := fzkLaw O K Δ L 1 fun _ => rfl
  by_cases h : φ (y⁻¹ * j a * y) ∈ ZK O K
  · obtain ⟨z, k, e⟩ := mem_ZK.1 h
    have hd : (1 : K) = (z : K) ^ 2 * algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).det := by
      have e1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K).det) e
      simp only [map_mul, map_inv, q3, Units.val_mul] at e1
      rw [Matrix.det_units_conj', Matrix.det_mul] at e1
      have e2 : ((jU j' a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        change (j' a).det = 1
        rw [ha, j_det_omega j' q2]
      rw [← e2, e1, RingHom.map_det]
      congr 1
      change (Matrix.scalar (Fin 2) (z : K)).det = _
      simp [Matrix.det_fin_two, sq]
    have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) O).det := (Matrix.GeneralLinearGroup.det k).isUnit
    obtain ⟨i, hi⟩ := hu.exists_right_inv
    have hi' := congrArg (algebraMap O K) hi
    rw [map_mul, map_one] at hi'
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : O, algebraMap O K z₀ = z := IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [show (z : K) ^ 2 = algebraMap O K i by linear_combination (-algebraMap O K i) * hd - (z : K) ^ 2 * hi']
      exact isIntegral_algebraMap))
    have hz1 : z₀ * (z₀ * (k : Matrix (Fin 2) (Fin 2) O).det) = 1 := IsFractionRing.injective O K (by
      rw [map_mul, map_mul, hz₀, map_one, hd]; ring)
    have hk : φ (y⁻¹ * j a * y) ∈ KG O K := by
      rw [e]
      refine mul_mem ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mkOfMulEqOne _ _ hz1), Units.ext ?_⟩ ⟨k, rfl⟩
      ext s t
      by_cases hst : s = t <;> simp [hst, hz₀]
    rw [e, F.2 z _ ⟨k, rfl⟩]
    exact (if_pos ((p1 _).1 hk)).trans (by simp)
  · rw [F.1 _ h]
    exact if_neg fun h' => h (Subgroup.mem_sup_right ((p1 _).2 h'))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinD
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finD : UpperTheory.V.Z.Sym.Loc.FinD := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj
  obtain ⟨φ, h1, h2, -, h4⟩ := dIso O K Δ L
  obtain ⟨j', hj'γ, hj'tr, hj'⟩ := h4 τ γ j hγ hj
  have hZD : ∀ g : DX Δ, g ∈ ZD Δ ↔ ∃ z, IsScal z g := by
    intro g
    simp only [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.comp_apply, IsScal]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
      rw [← hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      rw [show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Glob.mt g from rfl, hz]
      first | rfl | simp [Matrix.GeneralLinearGroup.scalar]
  have hmap : (ZD Δ ⊔ KD Δ O).map φ.toMonoidHom = ZK O K := by
    rw [Subgroup.map_sup]
    unfold ZK
    congr 1
    · ext x
      rw [Subgroup.mem_map_equiv, hZD, MonoidHom.mem_range]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z, by rw [← (h2 z _).1 hz]; simp⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, (h2 z _).2 (by simp)⟩
    · ext x
      rw [Subgroup.mem_map_equiv, ← h1]
      simp
  have hmem : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := by
    intro g
    rw [← hmap, Subgroup.mem_map_equiv]
    simp
  have hgen : ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 → ∃ S : Finset (DX Δ), ∀ y : DX Δ,
      y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ s ∈ S, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * s * u := by
    intro z hz
    obtain ⟨s, hs⟩ := finG O K Δ τ L hτ j' hj'tr z hz
    refine ⟨s.image φ.symm, ?_⟩
    intro y hy
    rw [hmem] at hy
    simp only [map_mul, map_inv, hj'] at hy
    obtain ⟨t, x, hx, k, hk, hyk⟩ := hs (φ y) hy
    refine ⟨t, φ.symm x, Finset.mem_image_of_mem _ hx, φ.symm k, by rw [hmem]; simp [hk], ?_⟩
    apply φ.injective
    simp [map_mul, hj', hyk]
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have hγa : γ = j a := by
    apply φ.injective
    rw [hj']
    apply Units.ext
    rw [← hj'γ]
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hgen a (by rw [ha]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    have hK : y⁻¹ * γ * y ∈ KD Δ O := by
      by_contra hn
      apply hy
      simp [one, hn]
    rw [← hγa]
    exact Subgroup.mem_sup_right hK
  · intro z hz χ
    obtain ⟨S, hS⟩ := hgen z (by rw [hz]; simp)
    refine ⟨S, ?_⟩
    intro y hy
    apply hS y
    unfold fZD at hy
    split_ifs at hy with hh
    · obtain ⟨z0, s0, hsc, hk⟩ := hh
      have hs0 : s0 ∈ ZD Δ := (hZD s0).2 ⟨z0, hsc⟩
      have := (ZD Δ ⊔ KD Δ O).mul_mem (Subgroup.mem_sup_left hs0) (Subgroup.mem_sup_right hk)
      simpa using this
    · exact absurd rfl hy
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hst : Subgroup.comap j (MulAction.stabilizer (DX Δ) (g : DX Δ ⧸ ZD Δ ⊔ KD Δ O)) =
        Subgroup.comap (jU j') (Subgroup.comap (MulAut.conj (φ g)⁻¹).toMonoidHom (ZK O K)) := by
      ext t
      simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk,
        smul_eq_mul, QuotientGroup.eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← Subgroup.inv_mem_iff, show ((j t * g)⁻¹ * g)⁻¹ = g⁻¹ * j t * g by group, hmem]
      simp [hj']
    rw [hst]
    exact stabG O K Δ τ L hτ j' hj'tr (φ g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem vcount_one_add {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (x : Etau K τ) :
    vcount O τ (1 + x) = vcount O τ x := by
  have key : ∀ X, (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (1 + x) * y ∈ S) ∧ X = cls τ S) ↔
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) := by
    intro X
    apply exists_congr
    intro S
    constructor
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      have h2 := (Submodule.span O (s : Set (Etau K τ))).sub_mem h1 hy
      simpa [add_mul] using h2
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      rw [add_mul, one_mul]
      exact (Submodule.span O (s : Set (Etau K τ))).add_mem hy h1
  unfold vcount
  congr 1
  funext X
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((key X).1 h1) h2
  · exact absurd ((key X).2 h2) h1
  · rfl

theorem UpperTheory.V.Z.Sym.Loc.gVals : UpperTheory.V.Z.Sym.Loc.GVals := by
  intro O K _ _ _ _ _ Δ τ L hτ hτO j χ hj hχ a ha z hz
  obtain ⟨o, ho⟩ := hτO
  have hna : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha]
    simp [QuadraticAlgebra.norm]
  have hnz : QuadraticAlgebra.norm (z : Etau K τ) = 2 + τ := by
    rw [hz]
    simp [QuadraticAlgebra.norm]
    ring
  have gA : gOrb O j χ a = vcount O τ a := by
    have h1 := gLat O K Δ τ L hτ j χ hj hχ a 1 1 (by rw [hna]; simp)
    simpa using h1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z 1 u (by rw [hnz, hu]; simp)
    simp only [map_one, Units.val_one, inv_one, one_mul, one_smul] at gZ
    rw [gA, gZ, hz, ← ha, vcount_one_add]
  · rintro ⟨u, hu⟩
    rw [gA, ha]
    apply vMax O K Δ τ L hτ
    · exact ⟨o, by rw [ho]; simp [trace]⟩
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · exact ⟨u, by rw [hu]; simp⟩
  · rintro ⟨u, hu⟩ s ε hs
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z s ε (by rw [hnz, hs])
    haveI := L.frac
    have hsO : ∃ c : O, algebraMap O K c = (s : K) := by
      have hint : IsIntegral O ((s : K) ^ 2) := by
        have : (s : K) ^ 2 = algebraMap O K (((ε⁻¹ : Oˣ) : O) * (2 + o)) := by
          have hinv : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [map_mul, map_add (f := _), map_ofNat, ho]
          linear_combination (-(algebraMap O K ((ε⁻¹ : Oˣ) : O))) * hs - (s : K) ^ 2 * hinv
        rw [this]
        exact isIntegral_algebraMap
      exact IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos hint)
    obtain ⟨c, hc⟩ := hsO
    have hs0 := s.ne_zero
    have hv : vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ)) = 1 := by
      apply vMax O K Δ τ L hτ
      · refine ⟨ε * c, ?_⟩
        rw [hz]
        simp [trace]
        rw [hc]
        field_simp
        linear_combination -hs
      · refine ⟨ε, ?_⟩
        rw [hz]
        simp [QuadraticAlgebra.norm]
        field_simp
        linear_combination -hs
      · refine ⟨-(ε * u), ?_⟩
        rw [hz]
        simp
        rw [hu]
        field_simp
        linear_combination (2 - τ) * hs
    rw [gZ, hv, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LocNorm
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.locNorm : UpperTheory.V.Z.Sym.Loc.LocNorm := by
  rintro O K _ _ _ _ _ Δ τ L ⟨τ₀, e₀⟩
  by_cases h1 : IsUnit (2 + τ₀)
  · obtain ⟨lam, -, hl⟩ := normEx O K Δ L h1.unit
    have ep : algebraMap O K (2 + τ₀) = 2 + τ := by simp [map_ofNat, e₀]
    rw [IsUnit.unit_spec, ep] at hl
    have h0 : 2 + τ ≠ 0 := ep ▸ (h1.map _).ne_zero
    have hll : lam * star lam = algebraMap K _ (2 + τ) := by rw [← hl, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    refine ⟨lam • ofE Δ ((2 + τ)⁻¹ • (1 + ω : Etau K τ)), ?_⟩
    have s1 : ∀ x : Etau K τ, sigL (lam • ofE Δ x) = star lam • ofE Δ x := fun x => by ext <;> simp [sigL, ofE]
    rw [s1, smul_mul_smul_comm, hll]
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · obtain ⟨x, y, -, hu, hn⟩ := rootEx O K Δ τ L τ₀ (-1) e₀ (by simpa [add_comm] using h1)
    obtain ⟨ν, -, hν⟩ := normEx O K Δ L (-1)
    exact ⟨_, (datFormM O K Δ τ L 1 _ (by simpa using hu) hn ν (by simpa using hν) 1 one_ne_zero).1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormOneIsCoboundaryUnramifiedQuadratic
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.h90L : UpperTheory.V.Z.Sym.Loc.NormOneIsCoboundaryUnramifiedQuadratic := by
  intro O K _ _ _ _ _ Δ L β hβ
  haveI := L.frac
  have h2 := L.two_ne
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  rw [QuadraticAlgebra.norm_def] at hβ
  by_cases h : 1 + β.re = 0
  · have h1 : β.re = -1 := by linear_combination h
    have h3 : β.im = 0 := by
      have : Δ * β.im ^ 2 = 0 := by rw [h1] at hβ; linear_combination -hβ
      simpa [h0] using this
    have hu : IsUnit (ω : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def, h0])
    exact ⟨hu.unit, by ext <;> simp [h1, h3]⟩
  · have hu : IsUnit (⟨1 + β.re, -β.im⟩ : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by
      have : QuadraticAlgebra.norm (⟨1 + β.re, -β.im⟩ : Lsq K Δ) = 2 * (1 + β.re) := by
        rw [QuadraticAlgebra.norm_def]; simp only; linear_combination hβ
      rw [this]; exact (mul_ne_zero h2 h).isUnit)
    refine ⟨hu.unit, ?_⟩
    ext
    · simp; linear_combination -hβ
    · simp; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OneD
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.oneD : UpperTheory.V.Z.Sym.Loc.OneD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j h1 h2 hγ hD
  obtain ⟨φ, p1, p2, p3, p4⟩ := dIso O K Δ L
  obtain ⟨j', q1, q2, q3⟩ := p4 τ γ j h1 h2
  have sc : ∀ z : Kˣ, IsScal z (φ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) := fun z => (p2 _ _).2 (by simp)
  have hZ : ∀ g, g ∈ ZD Δ ⊔ KD Δ O ↔ φ g ∈ ZK O K := fun g => by
    constructor
    · intro h
      refine (sup_le ?_ ?_ : ZD Δ ⊔ KD Δ O ≤ (ZK O K).comap φ.toMonoidHom) h
      · rintro s ⟨z, hz⟩
        exact Subgroup.mem_sup_left ⟨z, ((p2 z s).1 (congrArg Units.val hz).symm).symm⟩
      · exact fun k hk => Subgroup.mem_sup_right ((p1 k).2 hk)
    · intro h
      obtain ⟨z, k, e⟩ := mem_ZK.1 h
      rw [← φ.symm_apply_apply g, e, map_mul]
      exact mul_mem (Subgroup.mem_sup_left ⟨z, Units.ext (sc z).symm⟩) (Subgroup.mem_sup_right ((p1 _).1 (by rw [φ.apply_symm_apply]; exact ⟨k, rfl⟩)))
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have ea : j a = γ := φ.injective (by rw [q3]; exact Units.ext (by rw [← q1, ← ha]; rfl))
  have back : ∀ y t x k, k ∈ ZK O K → φ y = jU j' t * x * k → ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * φ.symm x * u := fun y t x k hk e =>
    ⟨φ.symm k, (hZ _).2 (by simpa using hk), φ.injective (by simp [e, q3])⟩
  obtain ⟨k₀, hk₀⟩ := (p1 γ).2 hγ
  obtain ⟨G1, G2⟩ := oneG O K Δ τ L j' q2 (fun s t => ⟨k₀ s t, by rw [q1, ← hk₀]; rfl⟩) hD
  have main : ∀ z : (Etau K τ)ˣ, ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) → ∀ y, y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O →
      ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u := fun z hz y hy => by
    obtain ⟨t, k, hk, e⟩ := ((G2 z hz).2 (φ y)).1 (by simpa [q3] using (hZ _).1 hy)
    obtain ⟨u, hu, e'⟩ := back y t 1 k hk (by simpa using e)
    exact ⟨t, u, hu, by simpa using e'⟩
  refine ⟨?_, ea ▸ main a (.inl ha), fun z hz => ⟨(p1 _).1 (q3 z ▸ (G2 z (.inr hz)).1), main z (.inr hz)⟩⟩
  rw [← G1]
  ext t
  rw [Subgroup.mem_comap, Subgroup.mem_comap, hZ, q3]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.ramUnit : UpperTheory.V.Z.Sym.Loc.RamUnit := by
  intro O K _ _ _ _ _ Δ L D h0 hD
  obtain ⟨ε, hε⟩ := L.exists_nonsq
  refine ⟨ε, if_neg fun h => ?_⟩
  obtain ⟨a, b, e⟩ := nm_symm h0 L.two_ne h (ε.isUnit.map _).ne_zero
  exact hD (e ▸ L.even_of_norm ε hε (e ▸ h0))
end

