module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberCovering
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriCharacterExtendingTorusCharacter
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_iwahori_character_extending_torus_character :
    ∀ (G : Type) [Group G] (I : Iwa G) (B : Type) [CommGroup B] (c : ℕ) (φ : I.T →* B), (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → ∃ ψ : I.Iw c →* B, ∀ b : I.Iw c, ((b : G) ∈ I.N → ψ b = 1) ∧ ((b : G) ∈ I.Nm c → ψ b = 1) ∧ ∀ hb : (b : G) ∈ I.T, ψ b = φ ⟨b, hb⟩ := by
  intro G _ I B _ c φ hφ
  obtain ⟨tt, h1, htt⟩ := UpperTheory.exists_iwahori_torus_projection G I
  have hle : ∀ b ∈ I.Iw c, b ∈ I.Iw 0 := by
    intro b hb
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 hb
    exact (UpperTheory.V.Hi.iwMem G I 0 b).1.2 ⟨x, hx, t, ht, y, I.Nm_anti (Nat.zero_le c) hy, h⟩
  have key : ∀ b ∈ I.Iw 0, ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c,
      φ (tt (b * (x * t * y))) = φ (tt b) * φ t := by
    intro b hb x hx t y hy
    have hx0 : x ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 x).1.2 ⟨x, hx, 1, one_mem _, 1, one_mem _, by simp⟩
    have ht0 : (t : G) ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 t).1.2 ⟨1, one_mem _, t, t.2, 1, one_mem _, by simp⟩
    have hbx := mul_mem hb hx0
    obtain ⟨s, hs, e⟩ := (htt _ (mul_mem hbx ht0)).2.2 c y hy
    have e0 : b * (x * t * y) = b * x * t * y := by group
    rw [e0, e, map_mul, hφ s hs, mul_one, ((htt _ hbx).1 t).2, (htt b hb).2.1 x hx, map_mul]
  have key1 : ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c, φ (tt (x * t * y)) = φ t := by
    intro x hx t y hy
    have := key 1 (one_mem _) x hx t y hy
    rwa [one_mul, h1, map_one, one_mul] at this
  refine ⟨MonoidHom.mk' (fun b => φ (tt b)) ?_, fun b => ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩⟩
  · intro a b
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 b.2
    have e1 := key a (hle _ a.2) x hx ⟨t, ht⟩ y hy
    have e2 := key1 x hx ⟨t, ht⟩ y hy
    show φ (tt ((a : G) * b)) = φ (tt a) * φ (tt b)
    rw [h, e2]
    exact e1
  · simpa using key1 b hb 1 1 (one_mem _)
  · simpa using key1 1 (one_mem _) 1 b hb
  · simpa using key1 1 (one_mem _) ⟨b, hb⟩ 1 (one_mem _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSectionAutomorphicSpaceWithPrescribedValue
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_section_automorphicSpace_with_prescribed_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U : Subgroup X.Ub, X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v, s v ∈ X.Sp τ θ U ∧ (∀ i j, s v (x i) j = v (i, j)) ∧ ∀ k : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∀ y ∈ X.I.Nm c, X.rp A m y (s v) - s v ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U hF c N x hcov huniq
  unfold Iwa.ContChar at hθ
  obtain ⟨tt, htt1, htt⟩ := UpperTheory.exists_iwahori_torus_projection Gp X.I
  obtain ⟨s, hs⟩ := UpperTheory.exists_linear_section_automorphicFunctions_of_free Γ Ga Gp X A m τ θ U hF c N x hcov huniq tt
    (fun b hb t => ((htt b hb).1 t).1)
  have hN_le : X.I.N ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_left.trans le_sup_left
  have hT_le : X.I.T ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right.trans le_sup_left
  have hNm_le : X.I.Nm c ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right
  have hIw0 : X.I.Iw c ≤ X.I.Iw 0 := by
    unfold Iwa.Iw
    exact sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  have key : ∀ (k : ℕ) (a e w : A), e - 1 ∈ maximalIdeal A ^ k → a * (e * w) - a * w ∈ maximalIdeal A ^ k := by
    intro k a e w h
    rw [show a * (e * w) - a * w = (a * w) * (e - 1) by ring]
    exact Ideal.mul_mem_left _ _ h
  have hright : ∀ (γ : Γ) (i : Fin N) (u : X.Ub) (b y : Gp),
      X.glob γ * x i * ((u : Ga), b) * (1, y) = X.glob γ * x i * ((u : Ga), b * y) := by
    intro γ i u b y
    rw [mul_assoc]
    exact congrArg _ (Prod.ext (mul_one _) rfl)
  have hdiff : ∀ v (k c' : ℕ), c ≤ c' → (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → (θ t : A) - 1 ∈ maximalIdeal A ^ k) →
      ∀ y ∈ X.I.Nm c', ∀ g j, s v (g * (1, y)) j - s v g j ∈ maximalIdeal A ^ k := by
    intro v k c' hcc' hk y hy g j
    obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
    have hb0 : b ∈ X.I.Iw 0 := hIw0 hb
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hcc' hy
    obtain ⟨s0, hs0, hts⟩ := (htt b hb0).2.2 c' y hy
    have hby : b * y ∈ X.I.Iw c := mul_mem hb (hNm_le hyc)
    rw [hright, hs v γ i u hu (b * y) hby, hs v γ i u hu b hb, hts, map_mul, mul_inv, Units.val_mul, mul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply key
    have h := hk s0 hs0
    have hinv := Units.inv_mul (θ s0)
    have : (((θ s0)⁻¹ : Aˣ) : A) - 1 = -(((θ s0)⁻¹ : Aˣ) : A) * ((θ s0 : A) - 1) := by
      linear_combination hinv
    rw [this]
    exact Ideal.mul_mem_left _ _ h
  refine ⟨s, fun v => ⟨?_, ?_, ?_⟩⟩
  · unfold Frame.Sp Frame.Amb
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show (_ ∧ _ ∧ _ ∧ _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro γ' g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [show X.glob γ' * (X.glob γ * x i * ((u : Ga), b)) = X.glob (γ' * γ) * x i * ((u : Ga), b) by
          rw [map_mul]; simp only [mul_assoc], hs v _ i u hu b hb, hs v γ i u hu b hb]
      · unfold fixd
        show ∀ n ∈ X.I.N, _
        intro n hn
        funext g
        show s v (g * (1, n)) = s v g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * n) (mul_mem hb (hN_le hn)), hs v γ i u hu b hb,
          (htt b (hIw0 hb)).2.1 n hn]
      · intro t
        funext g
        show s v (g * (1, (t : Gp))) = _
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * t) (mul_mem hb (hT_le t.2)), Pi.smul_apply, hs v γ i u hu b hb,
          ((htt b (hIw0 hb)).1 t).2, map_mul, mul_inv, Units.val_mul,
          mul_comm (((θ (tt b))⁻¹ : Aˣ) : A), mul_smul]
      · intro k
        obtain ⟨c0, hc0⟩ := hθ k
        exact ⟨max c c0, fun y hy g j => hdiff v k (max c c0) (le_max_left _ _)
          (fun t ht => hc0 t (X.I.Tc_anti (le_max_right _ _) ht)) y hy g j⟩
    · unfold fixd
      show ∀ u' ∈ U, _
      intro u' hu'
      funext g
      rw [Frame.ra_apply]
      obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
      rw [show X.glob γ * x i * ((u : Ga), b) * ((u' : Ga), 1) =
            X.glob γ * x i * (((u * u' : X.Ub) : Ga), b) by
          rw [mul_assoc]; exact congrArg _ (Prod.ext rfl (mul_one _)),
        hs v γ i (u * u') (mul_mem hu hu') b hb, hs v γ i u hu b hb, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, show u' * (u * u')⁻¹ = u⁻¹ by group]
  · intro i j
    have e : x i = X.glob 1 * x i * (((1 : X.Ub) : Ga), (1 : Gp)) := by simp
    rw [e, hs v 1 i 1 U.one_mem 1 (X.I.Iw c).one_mem, htt1]
    simp
  · intro k hk y hy
    unfold Frame.valIn
    rw [Submodule.mem_pi]
    intro g _
    rw [Submodule.mem_pi]
    intro j _
    exact hdiff v k c le_rfl hk y hy g j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberLevelFinite
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem comap_relIndex_ne_zero {G H : Type} [Group G] [Group H] (p : G →* H) (A B : Subgroup H)
    (T : Subgroup G) (hAB : A.relIndex B ≠ 0) (hT : ∀ g ∈ T, p g ∈ B) : (A.comap p).relIndex T ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h
  exact hAB (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.mpr hT) h)

private theorem finset_relIndex_ne_zero {G I : Type} [Group G] (H : I → Subgroup G) (T : Subgroup G) (S : Finset I)
    (h : ∀ v ∈ S, (H v).relIndex T ≠ 0) : ∃ W : Subgroup G, W.relIndex T ≠ 0 ∧ ∀ v ∈ S, W ≤ H v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨W, hW, hWS⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    refine ⟨H a ⊓ W, Subgroup.relIndex_inf_ne_zero (h a (Finset.mem_insert_self a S)) hW, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact inf_le_left
    · exact inf_le_right.trans (hWS v hv)

theorem UpperTheory.orbitalFiber_level_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.LevFin := by
  unfold Fib.LevFin
  intro F _ _ Δ D hD
  have hDet : Fib.DetOne := UpperTheory.orbitalFiber_det_eq_one
  unfold Fib.DetOne at hDet
  set P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) with hP
  have hle : ∀ v, D.J2v v ≤ KD ((cv v) Δ) (Ov v) := by
    intro v
    rw [Dat.J2v.eq_1]
    split_ifs with hv
    · exact SigOk.levelTwoLeIntegral (hD.sig v hv)
    · exact le_rfl
  have hT : ∀ v, ∀ g ∈ D.UZ ⊓ SA Δ, P.p v g ∈ KD ((cv v) Δ) (Ov v) := by
    intro v g hg
    have h1 : g ∈ D.UZ := hg.1
    have h2 : g ∈ SA Δ := hg.2
    rw [Dat.UZ.eq_1, RPG.box.eq_1, Subgroup.mem_iInf] at h1
    rw [SA.eq_1, Subgroup.mem_iInf] at h2
    have a := h1 v
    have b := h2 v
    rw [Subgroup.mem_comap] at a b
    exact hDet _ _ _ _ (sup_le_sup_left (hle v) _ a) b
  have hfin : ∀ v ∈ D.Sg, ((D.J2v v).comap (P.p v)).relIndex (D.UZ ⊓ SA Δ) ≠ 0 := by
    intro v hv
    apply comap_relIndex_ne_zero (P.p v) (D.J2v v) (KD ((cv v) Δ) (Ov v))
    · rw [Dat.J2v.eq_1, if_pos hv]
      exact SigOk.levelTwoFiniteIndex (hD.sig v hv)
    · exact hT v
  obtain ⟨W, hW, hWS⟩ := finset_relIndex_ne_zero (fun v => (D.J2v v).comap (P.p v)) _ D.Sg hfin
  have hsub : W ⊓ (D.UZ ⊓ SA Δ) ≤ D.U2 := by
    intro g hg
    rw [Dat.U2.eq_1, RPG.box.eq_1, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    by_cases hv : v ∈ D.Sg
    · exact hWS v hv hg.1
    · have e := hT v g hg.2
      rw [Dat.J2v.eq_1, if_neg hv]
      exact e
  refine ⟨?_, ?_⟩
  · rw [Dat.U2.eq_1, Dat.UZ.eq_1, RPG.box.eq_1, RPG.box.eq_1]
    exact iInf_mono fun v => Subgroup.comap_mono le_sup_right
  · intro h
    apply hW
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_eq_zero_of_le_left hsub h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberMasterFormula
section
open MulAction in
theorem UpperTheory.symmetric_fiber_master_formula :
    UpperTheory.V.Z.Sym.Glob.Fib.Master := by
  intro Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab
  classical
  haveI hSN : S.Normal := ⟨fun s hs g => by
    have h := S.mul_mem (hcomm g s) hs
    simpa [mul_assoc] using h⟩
  have hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype := MonoidHom.ext fun γ => hι₁ γ
  have hsub : Γ₁ ≤ S.comap ι := fun γ hγ => by
    have h := (ι₁ ⟨γ, hγ⟩).2
    rw [hι₁] at h
    exact h
  have hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite := fun g =>
    UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)

  have hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 := by
    have hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'} := by
      intro z hz
      have hz' : (z : Γ) ∈ Γ₀ := Subgroup.mem_subgroupOf.1 hz
      have h := htriv _ hz' ((1 : G) : G ⧸ U')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h
      have h' : ι z ∈ U' := by simpa using U'.inv_mem h
      simpa [hι₁] using h'
    haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype
    exact Nat.card_pos.ne'
  have hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    refine UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_
    · obtain ⟨T, hT1⟩ := hfinT 1
      refine ⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩
      have e' := congrArg (Subtype.val) e
      simpa [hι₁] using e'
    · have h := hstab ((1 : G) : G ⧸ U')
      rwa [MulAction.stabilizer_quotient] at h
  have hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) /
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
    have h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
    have h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    exact div_pos (mul_pos h1 h2) h3
  intro I _ x Ux Φ hij hcov hUx hΦl hΦr
  rw [UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcover := UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx
    (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T, fun s => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 s
      exact ⟨h, t, ht, u, (hUx i u).2 hu, e⟩)
    hfinU'
  have hone := UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩
      have e' : s = ι h * t * u := by
        have e2 := congrArg (Subtype.val) e
        simpa [hι₁] using e2
      rw [e']
      group)
    hstab hd hn
  rw [hcover, hcomp]
  have hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U'
      ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hone
  rw [hC]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberTraceKernel
section
open MulAction UpperTheory.V.Z.Sym

private theorem smul_quotient_eq_self_iff_exists_conj_out (G : Type) [Group G] (U : Subgroup G) (y : G ⧸ U) (a : G) :
    a • y = y ↔ ∃ u ∈ U, (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out y))) u = a := by
  set g := Quotient.out y with hg
  have hy : ((g : G) : G ⧸ U) = y := Quotient.out_eq y
  rw [← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]
  constructor
  · intro h
    refine ⟨g⁻¹ * a * g, ?_, by group⟩
    have := inv_mem h
    simpa [mul_assoc] using this
  · rintro ⟨u, hu, rfl⟩
    have : (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem UpperTheory.symmetric_fiber_trace_kernel :
    UpperTheory.V.Z.Sym.Glob.Fib.TrKer := by
  intro Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf
  classical
  set s := Base.Tw.one B with hs
  let δ : ConjClasses Γ → Γ := fun i => Classical.choose (ConjClasses.exists_rep i)
  have hδ : ∀ i, ConjClasses.mk (δ i) = i := fun i => Classical.choose_spec (ConjClasses.exists_rep i)
  have hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b := by
    intro a b
    simp only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩
    · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩
  have hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x := by
    intro a x
    show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _
    simp only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]
    constructor
    · intro h; calc x * a = x * (x⁻¹ * a * x) := by rw [h]
        _ = a * x := by group
    · intro h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h]
        _ = a := by group
  have h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y := fun z hz y => by
    rw [Subgroup.mem_bot.mp hz, map_one, one_smul]
  have h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ) := fun h γ => by
    rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g := fun u hu g => by
    have hl := hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)
    have hr := hf.right ⟨u, hu⟩ g
    simp only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr
    rw [mul_assoc, hl, hr]
  have h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite := fun g =>
    (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)
  have h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x := fun i x => by
    rw [Subgroup.range_subtype, hCent]
  have h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i' := fun i i' h e => by
    rw [← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]; exact ⟨h, e.symm⟩
  have h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 →
      ∃ i h, γ = h * δ i * h⁻¹ := fun γ g _ => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))
    exact ⟨ConjClasses.mk γ, c, hc.symm⟩
  have h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0 := fun y => by
    have := hFin.stab (Quotient.out y)
    rw [hΓ₀] at this
    convert this using 2
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]
    exact smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)
  have hT := (Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by
      rw [← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]; exact (hRel _ _).mp h)
    (fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2
  have hP := UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ
    (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5
    hFin.cls h7 h8 h9 h10
  rw [hT, hP]
  refine finsum_congr fun i => ?_
  simp only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]
  congr 2
  rw [hΓ₀]; rfl
end

