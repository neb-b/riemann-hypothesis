module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
section
noncomputable section

namespace GlobalTheory.PrincInLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem exists_entries (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) :
    ∃ s : Matrix (Fin n) (Fin n) S, (β⁻¹ * x * β).1 = (1 + N • s).map S.subtype := by
  have h : ∀ j, ∃ c : Fin n → S, ∀ i, (β⁻¹ * x * β).1 i j = (1 : Matrix (Fin n) (Fin n) R) i j + N • (c i : R) := by
    intro j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨y, hy, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    refine ⟨fun i => ⟨_, (hH y).1 hy i⟩, fun i => ?_⟩
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    simp only [Matrix.mulVec_sub, e0, Matrix.mulVec_smul] at e1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Pi.sub_apply, sub_eq_iff_eq_add'] at e1
    rw [Units.val_mul, Units.val_mul, Matrix.one_apply]
    rw [Pi.single_apply] at e1
    exact e1
  choose c hc using h
  refine ⟨Matrix.of fun i j => c j i, Matrix.ext fun i j => ?_⟩
  rw [hc, Matrix.map_apply, Matrix.add_apply, map_add (f := _), Matrix.smul_apply, map_nsmul, Matrix.one_apply,
    Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem exists_int (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) (hx' : ∀ z ∈ H, ∃ y ∈ H, (x⁻¹).1 *ᵥ z - z = N • y) :
    ∃ y : GL (Fin n) S, β * Formalism.UG.bc S.subtype y * β⁻¹ = x ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k), (N : k) = 0 → Formalism.UG.bc φ y = 1 := by
  obtain ⟨s, hs⟩ := exists_entries S β x H N hH hx
  obtain ⟨t, ht⟩ := exists_entries S β x⁻¹ H N hH hx'
  have inj : Function.Injective (fun m : Matrix (Fin n) (Fin n) S => m.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : (1 + N • s) * (1 + N • t) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  have h2 : (1 + N • t) * (1 + N • s) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x⁻¹ * β * (β⁻¹ * x * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  refine ⟨⟨_, _, h1, h2⟩, ?_, fun k _ φ hN => ?_⟩
  · have : Formalism.UG.bc S.subtype (⟨_, _, h1, h2⟩ : GL (Fin n) S) = β⁻¹ * x * β := Units.ext hs.symm
    rw [this]; group
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change φ ((1 + N • s) i j) = (1 : Matrix (Fin n) (Fin n) k) i j
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, map_nsmul, nsmul_eq_mul, hN, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end Ring

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem swap_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    (fun i => Algebra.TensorProduct.comm F _ E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have hm : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have := Submodule.smul_mem (Formalism.L2.Herm.hatL (F := F) Λ) ⟨_, hm⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
    convert this using 1
    funext i
    change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

theorem smul_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (t : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (ht : t ∈ Formalism.L2.Herm.intAf F E) :
    ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      (Algebra.TensorProduct.comm F _ E).symm t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have gen : ∀ t : FiniteAdeleRing (𝓞 F) F ⊗[F] E, (∀ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      t • (fun i => a ⊗ₜ[F] x i) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
    intro t ht y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz => obtain ⟨a, ha, x, hx, rfl⟩ := hz; exact ht a ha x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  induction ht using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, c • x, Λ.smul_mem c hx, ?_⟩
      funext i
      change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E c) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure
        ⟨b * a, fun v => mul_mem (b.2 v) (ha v), x, hx, ?_⟩
      funext i
      change ((b : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rwa [map_one, one_smul]
  | add a b _ _ ha hb => intro y hy; rw [map_add (f := _), add_smul]; exact add_mem (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [map_mul, mul_smul]; exact ha _ (hb y hy)

theorem swap_symm_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (fun i => (Algebra.TensorProduct.comm F _ E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
  | smul c x _ hx =>
    have := smul_mem_hat Λ c.1 c.2 _ hx
    convert this using 1
    funext i
    exact map_mul (Algebra.TensorProduct.comm F _ E).symm c.1 (x i)

theorem cong_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      M *ᵥ z - z = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      M.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (swap_symm_mem_hat Λ z hz)
  refine ⟨_, swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [Pi.sub_apply, Pi.smul_apply, map_sub, map_nsmul, Matrix.mulVec, dotProduct, map_sum, map_mul,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

theorem swap_mem_UPts (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hg : g ∈ HR (FiniteAdeleRing (𝓞 F) F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom g ∈
      Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  refine Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (Formalism.UG.sigR σ _)
    (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom (RingHom.ext fun x => ?_) (JR _ J) g hg
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a x => rfl

end Swap

theorem eq_latC {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.Member.latC V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  rw [one_pow, Nat.cast_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at h1 h2
  ext x
  exact ⟨fun hx => by simpa using h2 x hx, fun hx => by simpa using h1 x hx⟩


set_option maxHeartbeats 800000 in
theorem finCong_mem_levEnv : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (N : ℕ) (k : GA D V), IsSDFrame V β Λ 1 → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → GlobalTheory.Member.FinCong V N k → (finHom V).rangeRestrict k ∈ (levEnv V β L).J := by
  intro D V β Λ L N k hΛ hN hk
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  have hSt : Lev.finE V k ∈ Formalism.L2.DIV.St β := ⟨y, hy'⟩
  have hr : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
    intro PP hP
    rw [← hy', Formalism.L2.DIV.redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)
  have hU : Lev.finE V k ∈ Formalism.L2.DIV.UA D.sp.cm V.gram :=
    swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k)
  change Lev.finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)
  refine ⟨⟨⟨⟨hU, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inl hP)]; exact one_mem _
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inr hP)]; exact one_mem _
  · have e : Formalism.L2.DIV.rTup β L (Lev.finE V k) = 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (Lev.finE V k)) = 1
      rw [hr PP.1 (Or.inl PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    show Formalism.L2.DIV.rTup β L (Lev.finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r))
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.PrincInLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddEqOfEven
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_root (D : D7) (u : D.host.E) (hu : u * D.host.conj u = 1) :
    ∃ b : D.host.Eˣ, (b : D.host.E) = u * D.host.conj b := by
  by_cases h : 1 + u = 0
  · have hs : D.host.sqrtMinusD ≠ 0 := by
      intro h0
      have := D.host.sqrtMinusD_sq
      rw [h0] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero
      exact hd (by linear_combination this)
    refine ⟨Units.mk0 _ hs, ?_⟩
    rw [Units.val_mk0, D.host.conj_sqrtMinusD]
    linear_combination D.host.sqrtMinusD * h
  · refine ⟨Units.mk0 _ h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination -hu

theorem char_value {D : D7} {N : ℕ} (χ : HeckeU D N) (ep : ℤ) (u : D.host.E) (b : D.host.Eˣ)
    (hb : (b : D.host.E) = u * D.host.conj b) (k : D.what₂.Tau → ℤ) (hk : ∀ τ, 2 * k τ = ep * χ.n τ) :
    ((χ.f (Units.map (inc D).toMonoidHom b) ^ ep : ℂˣ) : ℂ) = ∏ τ, embT D τ u ^ (-(k τ)) := by
  rw [Units.val_zpow_eq_zpow_val, eq_inv_of_mul_eq_one_left (χ.aut b), inv_zpow, ← Finset.prod_zpow,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm, ← hk, zpow_mul, zpow_neg]
  congr 2
  have h0 : embT D τ b ≠ 0 := (map_ne_zero _).2 b.ne_zero
  have h1 := congrArg (embT D τ) hb
  rw [map_mul, embT_conj] at h1
  have h2 : (starRingEnd ℂ) (embT D τ b) ≠ 0 := (map_ne_zero _).2 h0
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h0, div_eq_iff h2]
  exact h1

theorem det_norm {D : D7} {n : ℕ} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : γ * (γ.map D.host.conj).transpose = 1) : γ.det * D.host.conj γ.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [← this]
  congr 1
  exact RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ

theorem det_root {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D g γ) (b : D.host.Eˣ) (hb : (b : D.host.E) = γ.det * D.host.conj b) :
    Units.map (inc D).toMonoidHom b =
      Matrix.GeneralLinearGroup.det g * sgU D (Units.map (inc D).toMonoidHom b) := by
  ext
  change inc D b = (g : Matrix (Fin n) (Fin n) (AE D)).det * sgA D (inc D b)
  rw [GlobalTheory.NormSum.PtsMem.sgA_inc, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← hb]

theorem isRat_one (D : D7) (n : ℕ) : IsRat D ((1 : GA D n) : GL (Fin n) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem moves_one (D : D7) (n : ℕ) : Moves D ((1 : GA D n) : GL (Fin n) (AE D)) (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
  exact h2 ▸ (h1 1).1

theorem exists_factor {D : D7} {n : ℕ} (g : GA D n) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    ∃ (g₁ g₂ : GA D n) (γ₁ γ₂ : Matrix (Fin n) (Fin n) D.host.E), IsRat D (g₁ : GL (Fin n) (AE D)) γ₁ ∧
      IsRat D (g₂ : GL (Fin n) (AE D)) γ₂ ∧ g = g₁ * g₂ ∧ γ = γ₁ * γ₂ ∧ (1 - γ₁).det ≠ 0 ∧ (1 - γ₂).det ≠ 0 := by
  obtain ⟨-, -, hex, hun, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D n
  obtain ⟨z, hz, hz1, hdet⟩ := _root_.GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero D n γ
  have hγ := hun g γ h
  obtain ⟨g₁, hg₁⟩ := hex (z • γ) (by
    have : (z • γ).map D.host.conj = D.host.conj z • γ.map D.host.conj := by
      ext i j; simp
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hγ, smul_smul, hz, one_smul])
  obtain ⟨g₂, hg₂⟩ := hex (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by
    have : (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)).map D.host.conj = z • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, conj_conj]
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_one, Matrix.mul_one,
      smul_smul, mul_comm, hz, one_smul])
  have e : γ = (z • γ) * (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]
  refine ⟨g₁, g₂, _, _, hg₁, hg₂, ?_, e, hdet, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    unfold IsRat at h hg₁ hg₂
    rw [Subgroup.coe_mul, Units.val_mul, h, hg₁, hg₂, ← Matrix.map_mul, ← e]
  · rw [show (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1 by
      rw [sub_smul, one_smul], Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h1 => hz1 ?_)
    rw [← conj_conj D z, ← h1, map_one]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ}

def IsPull (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ) : Prop :=
  ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z

theorem IsPull.mul {W : WeilO D cc δ N N' e0} {g₁ g₂ : GA D N} {g₁' g₂' : GA D N'}
    {γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E} {γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E} {a₁ a₂ : ℂ}
    (h₁ : IsPull W g₁ g₁' γ₁ γ₁' a₁) (h₂ : IsPull W g₂ g₂' γ₂ γ₂' a₂) :
    IsPull W (g₁ * g₂) (g₁' * g₂') (γ₁ * γ₂) (γ₁' * γ₂') (a₁ * a₂) := by
  intro F hF
  rw [W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]
  funext z
  simp only [pull_eq, mulV_mulV, adj_mul, mul_assoc]

theorem isPull_row (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E), IsRat D (g : GL (Fin N) (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine _root_.GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum D cc δ hc N N' e0 he (_root_.GlobalTheory.ThetaSpan.theta_span D cc δ hc N N' e0 he W.nz) W g 1 γ 1 _ h
      (isRat_one D N') ?_
    rw [_root_.GlobalTheory.VacuumExact.vacuum_exact D cc δ hc N N' hN hN' e0 he W g 1 _ 1 (Lt g) (stdL D N') (det_root h b hb) (by simp)
      (hLt g).1 (moves_one D N'), _root_.GlobalTheory.RatRow.pull_eq_smul_iop D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, one_mul, char_value W.chV' W.ep' γ.det b hb (fun τ => a τ + ((N' / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN'; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu))]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

theorem isPull_col (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep * W.chV.n τ + (N : ℤ)) (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E)
    (h : IsRat D (g : GL (Fin N') (AE D)) γ) : IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E), IsRat D (g : GL (Fin N') (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N'
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine _root_.GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum D cc δ hc N N' e0 he (_root_.GlobalTheory.ThetaSpan.theta_span D cc δ hc N N' e0 he W.nz) W 1 g 1 γ _
      (isRat_one D N) h ?_
    rw [_root_.GlobalTheory.VacuumExact.vacuum_exact D cc δ hc N N' hN hN' e0 he W 1 g 1 _ (stdL D N) (Lt g) (by simp) (det_root h b hb)
      (moves_one D N) (hLt g).1, _root_.GlobalTheory.RatEqui.pull_right_eq_det_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, mul_one, char_value W.chV W.ep γ.det b hb (fun τ => a τ - ((N / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_sub', sub_neg_eq_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu)), zpow_natCast]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

theorem oddEq_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 → oddEq D cc δ N N' e0 := by
  intro D cc δ hc t0 _ N N' hN hN' e0 he W γA γA' γ γ' a a' h h' ha' ha
  have := (isPull_row hc hN hN' he.1 W a ha γA γ h).mul (isPull_col hc hN hN' he.1 W a' ha' γA' γ' h')
  rw [mul_one, one_mul, mul_one, one_mul, ← Finset.prod_mul_distrib] at this
  exact this

end GlobalTheory.RatEqui
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlaceExtensionValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

namespace GlobalTheory.Proof.PlaceExtensionValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

end Coef

section Reps

variable {Gp Γ : Type} [Group Gp] [Group Γ] {ι : Γ →* Gp} {J : Subgroup Gp}


end Reps

section Row

open Formalism.IndefR.FWT

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ}

theorem isCoefExt_iff_c0BC (jL : D.what₂.LL →+* K') (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) :
    IsCoefExt jL (FWT.lamV D i) c₀ c' ↔ CoefficientBaseChange R i jL σ' c₀ c' := by
  constructor
  · intro h v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV jL _ _ v.2⟩, rfl, h v _ rfl⟩
  · intro h v v' hv
    obtain ⟨w, hw, hc⟩ := h v
    rw [show v' = w from Subtype.ext (hv.trans hw.symm)]
    exact hc

variable (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

variable {R i t c'}

variable {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
  {c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W}
  {c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W} {jL : D.what₂.LL →+* K'}


variable (R)

end Row

end GlobalTheory.Proof.PlaceExtensionValues

end
end

