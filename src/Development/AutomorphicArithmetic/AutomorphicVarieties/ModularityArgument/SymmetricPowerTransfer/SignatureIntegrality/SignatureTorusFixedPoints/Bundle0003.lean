module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NormalD

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.kc_le (V : Lev k) : Kc k n (V.c + 1) ≤ V.J n := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu, t, l, hl, ht, hl', rfl⟩ := GlAx.udl _ (Ideal.pow_le_self (Nat.succ_ne_zero _)) y hy
  rw [map_mul, map_mul]
  refine mul_mem (mul_mem (V.N_le ⟨?_, u, rfl⟩) (V.TH_le (V.Tc_le_TH ⟨?_, _, ht, rfl⟩))) (V.Nm_le ⟨?_, l, hl', rfl⟩)
  · have h := (mem_unipB _).1 hu
    exact (mem_unipB _).2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩
  · refine ⟨fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i),
      fun i => (Valuation.integer.integers (valuation k)).one_of_isUnit (t i).isUnit, ?_⟩
    ext i j
    show _ = algebraMap 𝒪[k] k ((diagT _ _ t : Matrix _ _ _) i j)
    rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
    split_ifs
    · rfl
    · simp
  · have h := GlAx.mem_low.1 hl
    exact GlAx.mem_low.2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩

private theorem bd_mul {c : ℤ} {a : GL (Fin n) k} (ha : a ∈ KO k (Fin n)) (M : Matrix (Fin n) (Fin n) k)
    (hM : ∀ i j, valuation k (M i j) ≤ uniformizer k ^ c) (i j : Fin n) : valuation k ((a.val * M) i j) ≤ uniformizer k ^ c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun r _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 ha).1 i r) (hM r j)).trans_eq (one_mul _)

end

theorem UpperTheory.V.Z.Sym.Sig.memJ : UpperTheory.V.Z.Sym.Sig.MemJ := by
  intro k _ _ _ _ V n g
  rw [GlAx.unif_spec, ← zpow_natCast]
  constructor
  · intro hg
    refine ⟨GlAx.bd_zero.1 (GlAx.mem_KO.1 (V.J_le_KO hg)).1, ?_⟩
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 g hg
    have h0 : a * diagT k (Fin n) s ∈ KO k (Fin n) := mul_mem ha.2 (V.J_le_KO (V.dg_mem fun i => hs i trivial))
    have h1 := bd_mul h0 _ (GlAx.mem_Kc.1 hb.2).1
    have h2 := (mem_unipB _).1 ha.1
    have e : ∀ i j, ((a * diagT k (Fin n) s).val * (b.val - 1)) i j = (a * diagT k (Fin n) s * b).val i j - a.val i j * s j := fun i j => by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ← Units.val_mul, Units.val_mul a, val_diagT, mul_diagonal]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h1 i j
      rwa [e, h2.1 i j hij, zero_mul, sub_zero] at this
    · have h3 := h1 i i
      rw [e, h2.2, one_mul] at h3
      have h4 : valuation k (s i : k) = 1 := V.H_le (hs i trivial)
      generalize (a * diagT k (Fin n) s * b).val i i = x at h3
      have h5 : valuation k (x / s i - 1) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := by
        rw [div_sub_one (s i).ne_zero, map_div₀, h4, div_one]; exact h3
      have h6 : valuation k (x / s i) = 1 := by
        have := Valuation.map_one_add_of_lt _ (h5.trans_lt (zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega)))
        rwa [add_sub_cancel] at this
      exact ⟨Units.mk0 (x / s i) (fun h => by simp [h] at h6) * s i, mul_mem (V.le (mem_Uc.2 ⟨h6, h5⟩)) (hs i trivial), by simp⟩
  · rintro ⟨h1, h2, h3⟩
    choose s hs es using h3
    have h4 : ∀ i, valuation k (s i : k) = 1 := fun i => V.H_le (hs i)
    let U : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => if i < j then ⟨g.val i j / s j, by
      show valuation k _ ≤ 1
      rw [map_div₀, h4, div_one]; exact h1 i j⟩ else if i = j then 1 else 0
    have hU : U.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j h => by
        have h' : j < i := h
        simp [U, h'.ne', h'.le.not_gt])]
      simp [U]
    let u := GeneralLinearGroup.map (algebraMap 𝒪[k] k) (GeneralLinearGroup.mk'' U (by rw [hU]; exact isUnit_one))
    have eu : ∀ i j, u.val i j = if i < j then g.val i j / s j else if i = j then 1 else 0 := fun i j => by
      show ((U i j : 𝒪[k]) : k) = _
      simp only [U]
      split_ifs <;> rfl
    have hu : u ∈ (glIwa k n).N := ⟨(mem_unipB _).2 ⟨fun i j h => by simp [eu, h.ne', h.le.not_gt], fun i => by simp [eu]⟩, _, rfl⟩
    have h5 : u * dg s ∈ V.J n := mul_mem (V.N_le hu) (V.dg_mem hs)
    have h6 : ∀ i j, valuation k ((g.val - (u * dg s).val) i j) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := fun i j => by
      rw [Matrix.sub_apply, Units.val_mul, dg, val_diagT, mul_diagonal, eu]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h]
      · simp [es]
      · simpa [h.ne', h.le.not_gt] using h2 i j h
    have h7 : GlAx.Bd ((V.c + 1 : ℕ) : ℤ) ((u * dg s)⁻¹ * g) := fun i j => by
      have := bd_mul (V.J_le_KO (inv_mem h5)) _ h6 i j
      rwa [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel] at this
    have h8 : (u * dg s)⁻¹ * g ∈ KO k (Fin n) := by
      generalize (u * dg s)⁻¹ * g = x at h7
      have h9 := GlAx.bd_zero.1 (h7.mono (by omega))
      let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x.val i j, h9 i j⟩
      have hX : X.map (IsLocalRing.residue 𝒪[k]) = 1 := by
        ext i j
        have : X i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
          rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[k]), GlAx.mem_pow]
          have := h7.mono (show ((1 : ℕ) : ℤ) ≤ _ by omega) i j
          convert this using 2
          simp only [Matrix.sub_apply, Matrix.one_apply]
          split_ifs <;> rfl
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
        rw [map_apply, this]
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      have hd : IsUnit X.det := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hX, det_one]
        exact one_ne_zero
      exact ⟨GeneralLinearGroup.mk'' X hd, Units.ext rfl⟩
    have := mul_mem h5 (kc_le V (mem_Kc_of h8 h7))
    rwa [mul_inv_cancel_left] at this

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem quot0 {R : Type} [CommRing R] (I : Ideal R) (u v : R ⧸ I ^ 0) : u = v := by
  haveI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  exact Subsingleton.elim u v

private theorem mem_kc_zero_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (x : GL (Fin n) k) (hx : x ∈ KO k (Fin n)) :
    x ∈ Kc k n 0 := by
  obtain ⟨x0, rfl⟩ := hx
  refine ⟨x0, MonoidHom.mem_ker.2 ?_, rfl⟩
  exact Units.ext (Matrix.ext fun i j => quot0 _ _ _)

private theorem conj_mem_kc_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (m : ℕ) (t x : GL (Fin n) k) (ht : t ∈ KO k (Fin n))
    (hx : x ∈ Kc k n m) : t * x * t⁻¹ ∈ Kc k n m := by
  obtain ⟨t0, rfl⟩ := ht
  obtain ⟨x0, hx0, rfl⟩ := hx
  exact ⟨t0 * x0 * t0⁻¹, (MonoidHom.normal_ker _).conj_mem x0 hx0 t0, by simp [map_mul, map_inv]⟩

private theorem mem_ko_and_torus_of_mem_th {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (t : GL (Fin n) k) (ht : t ∈ V.TH n) :
    t ∈ KO k (Fin n) ∧ t ∈ (glIwa k n).T := by
  obtain ⟨d, hd, rfl⟩ := ht
  have hv : ∀ i, valuation k (d i : k) = 1 := fun i => V.H_le (hd i (Set.mem_univ i))
  refine ⟨?_, ⟨d, fun i => hv i, rfl⟩⟩
  have hO : ∀ i, (d i : k) ∈ 𝒪[k] := fun i => (Valuation.mem_integer_iff _ _).2 (hv i).le
  let d0 : Fin n → (𝒪[k])ˣ := fun i =>
    ((Valuation.integer.integers (valuation k)).isUnit_of_one' (x := ⟨d i, hO i⟩) (hv i)).unit
  refine ⟨diagT (𝒪[k]) (Fin n) d0, ?_⟩
  ext i j
  simp [diagT, leviEmb, leviTorus, Matrix.diagonal_apply]
  split_ifs <;> simp [d0] <;> rfl

private theorem map_mem_j_of_pres {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (σ : GL (Fin n) k →* GL (Fin n) k)
    (hσ : Pres V σ) (g : GL (Fin n) k) (hg : g ∈ V.J n) : σ g ∈ V.J n := by
  unfold Lev.J at hg ⊢
  have h : (glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c ≤
      ((glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c).comap σ := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;> rw [Subgroup.mem_comap]
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hσ.N x hx))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hσ.T x hx))
    · exact Subgroup.mem_sup_right (hσ.Nm V.c x hx)
  exact h hg

theorem UpperTheory.V.Z.Sym.Sig.contract : UpperTheory.V.Z.Sym.Sig.Contract := by
  intro k _ _ _ _ V n σ hσ d hd g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  have NJ : ∀ z ∈ (glIwa k n).N, z ∈ V.J n := fun z hz =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
  have NmJ : ∀ z ∈ (glIwa k n).Nm V.c, z ∈ V.J n := fun z hz => Subgroup.mem_sup_right hz
  have NKO : ∀ z ∈ (glIwa k n).N, z ∈ KO k (Fin n) := fun z hz => hz.2
  have NmKO : ∀ c, ∀ z ∈ (glIwa k n).Nm c, z ∈ KO k (Fin n) := fun c z hz =>
    Subgroup.map_le_range _ _ hz.2
  have hh : y * σ x ∈ V.J n := mul_mem hy (map_mem_j_of_pres V σ hσ x hx)
  have key : ∀ u : (glIwa k n).N, ∃ a ∈ (glIwa k n).N, ∃ s ∈ V.TH n, ∃ b ∈ (glIwa k n).Nm V.c,
      y * σ x * σ (u : GL (Fin n) k) = a * s * b := fun u =>
    (factJ k V n).1 _ (mul_mem hh (NJ _ (hσ.N _ u.2)))
  choose a ha s hs b hb hab using key
  let Ψ : (glIwa k n).N → (glIwa k n).N := fun u =>
    ⟨dg d * a u * (dg d)⁻¹,
      ((shrink k n d hd 0).1 (a u) (ha u) (mem_kc_zero_of_mem_ko _ (NKO _ (ha u)))).1⟩
  obtain ⟨u, hu⟩ := fixPt k n (glIwa k n).N (Or.inl rfl) Ψ (by
    intro m u1 u2 h12
    have e1 : (y * σ x * σ (u1 : GL (Fin n) k))⁻¹ * (y * σ x * σ (u2 : GL (Fin n) k)) =
        σ ((u1 : GL (Fin n) k)⁻¹ * u2) := by
      rw [map_mul, map_inv]
      group
    have h1 : (a u1 * s u1 * b u1)⁻¹ * (a u2 * s u2 * b u2) ∈ Kc k n m := by
      rw [← hab, ← hab, e1]
      exact hσ.K m _ h12
    have h2 := (factJ k V n).2 m _ (ha u1) _ (ha u2) _ (hs u1) _ (hs u2) _ (hb u1) _ (hb u2) h1
    have h3 := ((shrink k n d hd m).1 _ (mul_mem (inv_mem (ha u1)) (ha u2)) h2).2
    have e2 : ((Ψ u1 : GL (Fin n) k))⁻¹ * (Ψ u2 : GL (Fin n) k) =
        dg d * ((a u1)⁻¹ * a u2) * (dg d)⁻¹ := by
      simp only [Ψ]
      group
    rw [e2]
    exact h3)
  have hu' : dg d * a u * (dg d)⁻¹ = (u : GL (Fin n) k) := congrArg Subtype.val hu
  have ht := mem_ko_and_torus_of_mem_th V _ (hs u)
  have tinvT : (s u)⁻¹ ∈ (glIwa k n).T := inv_mem ht.2
  have memΨ : ∀ w ∈ (glIwa k n).Nm V.c,
      (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) ∈ (glIwa k n).Nm V.c := by
    intro w hw
    refine mul_mem (inv_mem (hb u)) ?_
    have h1 := ((shrink k n d hd 0).2 V.c (σ w) (hσ.Nm _ _ hw)
      (mem_kc_zero_of_mem_ko _ (NmKO _ _ (hσ.Nm _ _ hw)))).1
    have h2 := (glIwa k n).T_Nm V.c _ tinvT _ h1
    rwa [inv_inv] at h2
  let Ψ₂ : (glIwa k n).Nm V.c → (glIwa k n).Nm V.c := fun w => ⟨_, memΨ w w.2⟩
  obtain ⟨w, hw⟩ := fixPt k n ((glIwa k n).Nm V.c) (Or.inr ⟨V.c, rfl⟩) Ψ₂ (by
    intro m w1 w2 h12
    have e : ((Ψ₂ w1 : GL (Fin n) k))⁻¹ * (Ψ₂ w2 : GL (Fin n) k) =
        (s u)⁻¹ * ((dg d)⁻¹ * σ ((w1 : GL (Fin n) k)⁻¹ * w2) * dg d) * ((s u)⁻¹)⁻¹ := by
      simp only [Ψ₂]
      rw [map_mul, map_inv]
      group
    rw [e]
    refine conj_mem_kc_of_mem_ko _ _ _ (inv_mem ht.1) ?_
    have hmem : σ ((w1 : GL (Fin n) k)⁻¹ * w2) ∈ (glIwa k n).Nm V.c :=
      hσ.Nm _ _ (mul_mem (inv_mem w1.2) w2.2)
    exact ((shrink k n d hd m).2 V.c _ hmem (hσ.K m _ h12)).2)
  have hw' : (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) = (w : GL (Fin n) k) :=
    congrArg Subtype.val hw
  have comm : dg d * s u = s u * dg d :=
    (glIwa k n).comm _ ⟨d, rfl⟩ _ ((glIwa k n).T_le ht.2)
  refine ⟨x * u * σ w, mul_mem (mul_mem hx (NJ _ u.2)) (NmJ _ (hσ.Nm _ _ w.2)), s u, hs u, ?_⟩
  rw [map_mul, map_mul, hσ.invol]
  have E0 : (x * (u : GL (Fin n) k) * σ w)⁻¹ * (x * dg d * y) * (σ x * σ (u : GL (Fin n) k) * w) =
      (σ w)⁻¹ * ((u : GL (Fin n) k)⁻¹ * dg d * (y * σ x * σ (u : GL (Fin n) k)) * w) := by
    group
  have E4 : b u * (w : GL (Fin n) k) = (s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u := by
    conv_lhs => rw [← hw']
    group
  rw [E0, hab u, ← hu']
  have E5 : (dg d * a u * (dg d)⁻¹)⁻¹ * dg d * (a u * s u * b u) * (w : GL (Fin n) k) =
      dg d * s u * (b u * w) := by
    group
  rw [E5, E4, ← comm]
  group

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.DiagDC
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem vo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : kˣ) :
    valuation k (x : k) = uniformizer k ^ ord k x := by
  have h1 := GlAx.val_div_ord x
  have h2 := GlAx.val_zpow (k := k) (ord k x)
  have e : (x : k) = ((x / unif k ^ ord k x : kˣ) : k) * ((unif k ^ ord k x : kˣ) : k) := by
    rw [← Units.val_mul, div_mul_cancel]
  rw [e, map_mul, h1, h2, one_mul]

theorem UpperTheory.V.Z.Sym.Sig.diagDC : UpperTheory.V.Z.Sym.Sig.DiagDC := by
  intro k _ _ _ _ V n d s hd
  have hlt : uniformizer k < 1 := ValuativeRel.uniformizer_lt_one
  have hpos : 0 < uniformizer k := GlAx.unif_pos
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨x1, hx1, t1, ht1, y1, hy1, rfl⟩ := (factJ k V n).1 a ha
    obtain ⟨x2, hx2, t2, ht2, y2, hy2, hb'⟩ := (factJ k V n).1 b⁻¹ (inv_mem hb)
    obtain ⟨h1, hh1, rfl⟩ := ht1
    obtain ⟨h2, hh2, rfl⟩ := ht2
    have hb2 : b = (x2 * diagT k (Fin n) h2 * y2)⁻¹ := by rw [← hb', inv_inv]
    subst hb2
    have hY0 : (diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d ∈ (glIwa k n).Nm V.c := by
      have hv : ∀ i, valuation k ((d⁻¹ i : kˣ) : k) = uniformizer k ^ (-ord k (d i)) := by
        intro i
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, vo, _root_.zpow_neg]
      have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + -ord k (d j) ≤ (V.c : ℤ) + -ord k (d i) := by
        intro i j hji
        have h0 := hd j i hji.le
        rw [vo, vo, zpow_le_zpow_iff_right_of_lt_one₀ hpos hlt] at h0
        omega
      have := GlAx.conj_Nm hv hc hy1
      rwa [map_inv, inv_inv] at this
    have hY : (diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹ ∈ (glIwa k n).Nm V.c :=
      mul_mem hY0 (inv_mem hy2)
    have hY' : diagT k (Fin n) h2 * ((diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹) *
        (diagT k (Fin n) h2)⁻¹ ∈ (glIwa k n).Nm V.c := by
      have hv : ∀ i, valuation k ((h2 i : kˣ) : k) = uniformizer k ^ ((0 : Fin n → ℤ) i) := by
        intro i
        rw [Pi.zero_apply, zpow_zero]
        exact V.H_le (hh2 i (Set.mem_univ i))
      have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + (0 : Fin n → ℤ) j ≤ (V.c : ℤ) + (0 : Fin n → ℤ) i := by
        intro i j _
        simp
      exact GlAx.conj_Nm hv hc hY
    set Y' := diagT k (Fin n) h2 * ((diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹) *
        (diagT k (Fin n) h2)⁻¹ with hYq
    set T := diagT k (Fin n) (h1 * d * h2⁻¹) with hTq
    have hT : T = diagT k (Fin n) h1 * diagT k (Fin n) d * (diagT k (Fin n) h2)⁻¹ := by
      rw [hTq, map_mul, map_mul, map_inv]
    have hs : dg s = x1 * T * Y' * x2⁻¹ := by
      rw [hab, hT, hYq]
      group
    have hP1 : T⁻¹ * x1⁻¹ * T ∈ unipB k (Fin n) := by
      have := GlAx.conj_up (h1 * d * h2⁻¹)⁻¹ (inv_mem hx1.1)
      rwa [map_inv, inv_inv] at this
    have hP2 : T⁻¹ * (dg s * x2 * (dg s)⁻¹) * T ∈ unipB k (Fin n) := by
      have h0 := GlAx.conj_up s hx2.1
      have := GlAx.conj_up (h1 * d * h2⁻¹)⁻¹ h0
      rwa [map_inv, inv_inv] at this
    have hDu : diagT k (Fin n) ((h1 * d * h2⁻¹)⁻¹ * s) = T⁻¹ * dg s := by
      rw [map_mul, map_inv]
    have heq : (T⁻¹ * x1⁻¹ * T * (T⁻¹ * (dg s * x2 * (dg s)⁻¹) * T)) *
        diagT k (Fin n) ((h1 * d * h2⁻¹)⁻¹ * s) * Y'⁻¹ = 1 := by
      rw [hDu, hs]
      group
    have hu := (GlAx.uniq _ (mul_mem hP1 hP2) (inv_mem hY'.1) heq).2
    have hu1 : (h1 * d * h2⁻¹)⁻¹ * s = 1 := by
      funext i
      have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) hu
      simp only [val_diagT, diagonal_apply_eq, Units.val_one, one_apply_eq] at this
      exact Units.ext this
    have hs' : h1 * d * h2⁻¹ = s := inv_mul_eq_one.mp hu1
    intro i
    rw [← hs']
    have e : (h1 * d * h2⁻¹) i / d i = h1 i * (h2 i)⁻¹ := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (hh1 i (Set.mem_univ i)) (inv_mem (hh2 i (Set.mem_univ i)))
  · intro h
    refine ⟨1, one_mem _, diagT k (Fin n) (d⁻¹ * s), ?_, ?_⟩
    · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨d⁻¹ * s, fun i _ => ?_, rfl⟩)
      have := h i
      rwa [div_eq_mul_inv, mul_comm] at this
    · show diagT k (Fin n) s = 1 * diagT k (Fin n) d * diagT k (Fin n) (d⁻¹ * s)
      rw [one_mul, ← map_mul, mul_inv_cancel_left]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ModelD
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

private theorem eD_coe {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (g : DX Δ) :
    (eD hs g : Matrix (Fin 2) (Fin 2) K) = (mt g).map (proj hs) := by
  rfl

private theorem ev_coe {K : Type} [Field K] {τ a : K} (h : a * a = τ * a - 1) (z : (Etau K τ)ˣ) :
    (evU h z : K) = (z : Etau K τ).re + a * (z : Etau K τ).im := rfl

private theorem proj_smul {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (c : K) (x : Lsq K Δ) :
    proj hs (c • x) = c * proj hs x := by
  simp [proj]
  ring

theorem _root_.UpperTheory.V.Z.Sym.Sig.modelD : UpperTheory.V.Z.Sym.Sig.ModelD := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 a ha γ j ⟨hdet, htr⟩ hemb
  obtain ⟨-, -, -, -, hdt, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  have inj := (algebraMap k (Lsq k Δ)).injective
  have hdet1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 :=
    inj (by rw [← (hdt γ).1, hdet, map_one])
  have htr1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + ((a⁻¹ : kˣ) : k) :=
    inj (by rw [← (hdt γ).2, htr])
  have hprod : valuation k ((a⁻¹ : kˣ) : k) * valuation k (a : k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : a ≠ a⁻¹ := by
    intro h
    have h' : valuation k ((a⁻¹ : kˣ) : k) < 1 := by
      rw [← h]
      exact ha
    exact (mul_lt_of_le_one_of_lt h'.le ha).ne hprod
  have hcp : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
      (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) := by
    rw [Matrix.charpoly_fin_two, htr1, hdet1]
    have hab : (a : k) * ((a⁻¹ : kˣ) : k) = 1 := Units.mul_inv a
    rw [← hab, C_add, C_mul]
    ring
  obtain ⟨g₀, hg₀⟩ := normalD k (eD hs γ) a a⁻¹ hne hcp
  refine ⟨g₀, hg₀, fun t => ?_⟩
  apply Units.ext
  have hM : ((eD hs (j t) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).re • (1 : Matrix (Fin 2) (Fin 2) k) +
        (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).im • ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    rw [eD_coe, eD_coe, hemb t]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), proj_smul, Matrix.one_apply]
    split_ifs <;> simp
  have hg : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (g₀ : Matrix (Fin 2) (Fin 2) k) * ((dg ![a, a⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    rw [hg₀, Units.val_mul, Units.val_mul]
  have hPP : (g₀ : Matrix (Fin 2) (Fin 2) k) * ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hM, hg, Units.val_mul, Units.val_mul]
  unfold dg
  rw [val_diagT, val_diagT]
  have hdiag : (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).re • (1 : Matrix (Fin 2) (Fin 2) k) +
      (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).im • diagonal (fun i => ((![a, a⁻¹] i : kˣ) : k)) =
      diagonal fun i => ((![evU (root_left a) t, evU (root_right a) t] i : kˣ) : k) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.one_apply, Matrix.diagonal_apply, ev_coe] <;> ring
  rw [← hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP,
    Matrix.mul_smul, Matrix.smul_mul]

end UpperTheory.V.Z.Sym.Sig

end
end

