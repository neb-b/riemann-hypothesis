module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

section Pos

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {m : ℕ}

theorem fu_colSpan_map {k : ℕ} (γ : GL (Fin k) Kf) (h : Matrix (Fin k) (Fin k) Kf) :
    (colSpan O h).map (nt_phi O γ) = colSpan O ((γ : Matrix (Fin k) (Fin k) Kf) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

def fuT (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
  ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf).det ^ (-(lam (Fin.last m)))) •
    rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) F

theorem fu_nablaLTw (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ nablaLTw O Kf m lam h) :
    fuT γ lam F ∈ nablaLTw O Kf m lam ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h) := by
  obtain ⟨G, hG, rfl⟩ := hF
  have hcomp : (rowAct Kf ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h))
      ((rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)) G) = (rowAct Kf h) G := by
    have h1 := congrArg (fun φ => φ G) (rowActMul Kf (m + 1) (m + 1)
      ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h)
      ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    simp only [AlgHom.comp_apply] at h1
    rw [h1, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) G, ?_, ?_⟩
  · simp only [nablaL] at hG ⊢
    rw [SetLike.mem_coe, Submodule.mem_comap] at hG ⊢
    simpa only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, hcomp] using hG
  · simp only [fuT, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, map_smul, smul_smul,
      Matrix.det_mul, mul_zpow]

theorem invariant_sections_transport_GL (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (Λ : Submodule O (Fin (m + 1) → Kf)) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam Λ) : fuT γ lam F ∈ H0 O m lam (Λ.map (nt_phi O γ)) := by
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro g hg
  have hid : (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))).comp (nt_phi O γ) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.mulVec ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
      (Matrix.mulVec (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hback : (Λ.map (nt_phi O γ)).map (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))) = Λ := by
    rw [← Submodule.map_comp, hid, Submodule.map_id]
  have hΛ' : Λ = colSpan O (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g) :=
    hback.symm.trans (by rw [hg.2, fu_colSpan_map])
  have hdet : IsUnit (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g).det := by
    rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).mul hg.1
  have key := fu_nablaLTw (O := O) γ lam _ F (hF _ ⟨hdet, hΛ'⟩)
  rwa [← mul_assoc, Units.mul_inv, one_mul] at key

end Pos

section Tw

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ}

def fuF (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) : Qq →+* Kf := ι.comp ((σ ^ s : Qq ≃+* Qq) : Qq →+* Qq)

def fuG (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) : GL (Fin k) Kf :=
  Matrix.GeneralLinearGroup.map (fuF ι σ s) g

theorem fu_twist (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) (x : Fin k → Qq) :
    twistVec ι σ s (nt_phi W g x) = nt_phi O (fuG ι σ s g) (twistVec ι σ s x) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [twistVec, nt_phi, fuG, fuF, Matrix.mulVec, dotProduct, map_sum]

theorem fu_extO (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) (L : Submodule W (Fin k → Qq)) :
    extO O ι σ s (L.map (nt_phi W g)) = (extO O ι σ s L).map (nt_phi O (fuG ι σ s g)) := by
  unfold extO
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => fu_twist ι σ s g x

theorem fu_LeAt (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (s : ℕ) (g : GL (Fin k) Qq) (e : Edge W Qq k) :
    LeAt p ι σ w s (mapE g e) = (LeAt p ι σ w s e).map (nt_phi O (fuG ι σ s g)) := by
  rw [LeAt, LeAt, Submodule.map_sup, ← fu_extO]
  congr 1
  rw [Submodule.map_span]
  simp only [mapE, Submodule.map_coe, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  have key := fun y => fu_twist (W := W) (O := O) ι σ s g y
  simp only [nt_phi, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at key ⊢
  rw [← Matrix.mulVec_smul (g : Matrix (Fin k) (Fin k) Qq), key, Matrix.mulVec_smul]

end Tw

section Ten

variable {Kf : Type} [Field Kf] {n' m : ℕ}

def fuTT (lam0 : Fin n' → Fin (m + 1) → ℤ) (γ : Fin n' → GL (Fin (m + 1)) Kf) :
    MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
  (∏ s, ((γ s : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf).det ^ (-(lamAt lam0 s (Fin.last m))))) •
    (blockAct Kf (n := m + 1) fun s => (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)).toLinearMap

theorem fu_tensor {A : Type} [CommRing A] [Algebra A Kf] (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (γ : Fin n' → GL (Fin (m + 1)) Kf) (M M' : Fin n' → Submodule A (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
    (h : ∀ s F, F ∈ M s → fuT (γ s) (lamAt lam0 s) F ∈ M' s)
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hP : P ∈ tensorLat A Kf M) :
    fuTT lam0 γ P ∈ tensorLat A Kf M' := by
  have hle : tensorLat A Kf M ≤ (tensorLat A Kf M').comap ((fuTT lam0 γ).restrictScalars A) := by
    unfold tensorLat
    rw [Submodule.span_le]
    rintro Q ⟨F, hF, rfl⟩
    refine Submodule.subset_span ⟨fun s => fuT (γ s) (lamAt lam0 s) (F s), fun s => h s _ (hF s), ?_⟩
    simp only [LinearMap.coe_restrictScalars, fuTT, fuT, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      map_prod, ldtensor_blockAct_blockEmb, map_smul]
    simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  exact hle hP

theorem fu_block_inv {k n : ℕ} (A B : Fin n' → Matrix (Fin k) (Fin k) Kf) (h : ∀ s, B s * A s = 1)
    (P : MvPolynomial (Fin n' × (Fin k × Fin n)) Kf) : blockAct Kf A (blockAct Kf B P) = P := by
  have hc : (blockAct Kf A).comp (blockAct Kf B) = AlgHom.id Kf (MvPolynomial (Fin n' × Fin k × Fin n) Kf) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨s, a, j⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, AlgHom.id_apply, blockAct, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, h s,
      Matrix.one_apply]
    simp
  exact congrArg (fun φ => φ P) hc

theorem fuTT_inv (lam0 : Fin n' → Fin (m + 1) → ℤ) (γ : Fin n' → GL (Fin (m + 1)) Kf)
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :
    fuTT lam0 (fun s => (γ s)⁻¹) (fuTT lam0 γ P) = P := by
  simp only [fuTT, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, inv_inv]
  rw [fu_block_inv (fun s => ((γ s : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    (fun s => (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    (fun s => Units.inv_mul (γ s)), ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_smul]
  intro s _
  rw [← mul_zpow, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_zpow]

end Ten

theorem fu_Hten {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hDom : IsDominant lam0) (γ : Fin n' → GL (Fin (m + 1)) Kf) (Λ Λ' : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, Λ' s = (Λ s).map (nt_phi O (γ s))) (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :
    P ∈ Hten O lam0 Λ ↔ fuTT lam0 γ P ∈ Hten O lam0 Λ' := by
  have hant : ∀ s, Antitone (lamAt lam0 s) := by
    intro s i j hij
    unfold lamAt
    split_ifs
    · exact hDom s hij
    · simp only [neg_le_neg_iff]
      exact hDom s (Fin.rev_le_rev.mpr hij)
  unfold Hten
  constructor
  · intro hP
    refine fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [hΛ s]
    exact invariant_sections_transport_GL (γ s) _ (hant s) (Λ s) F hF
  · intro hP
    have hback : ∀ s, (Λ' s).map (nt_phi O (((γ s)⁻¹ : GL (Fin (m + 1)) Kf))) = Λ s := by
      intro s
      rw [hΛ s, ← Submodule.map_comp]
      convert Submodule.map_id (Λ s)
      refine LinearMap.ext fun x => ?_
      show Matrix.mulVec (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
        (Matrix.mulVec (γ s : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have key := fu_tensor lam0 (fun s => (γ s)⁻¹) (fun s => H0 O m (lamAt lam0 s) (Λ' s))
      (fun s => H0 O m (lamAt lam0 s) (Λ s)) (fun s F hF => ?_) _ hP
    · rwa [fuTT_inv] at key
    · beta_reduce at hF ⊢
      rw [← hback s]
      exact invariant_sections_transport_GL ((γ s)⁻¹) _ (hant s) (Λ' s) F hF

theorem restFunct : RestFunct := by
  intro p n' R m lam0 hDom g
  have hanti := kp_lamAt_antitone lam0 hDom
  have hV : ∀ (γ : Fin n' → GL (Fin (m + 1)) R.Kf), ∀ P ∈ Vsp R.Kf lam0, fuTT lam0 γ P ∈ Vsp R.Kf lam0 := by
    intro γ P hP
    refine fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP
    rw [if_pos (hanti s)] at hF ⊢
    exact Submodule.smul_mem _ _ (dualWeylRowStable R.Kf _ _ _ _ F hF)
  let γ : Fin n' → GL (Fin (m + 1)) R.Kf := fun s => fuG R.ι R.σ s.val g
  let T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0 :=
    LinearEquiv.ofLinearMap ((fuTT lam0 γ).restrict (hV γ)) ((fuTT lam0 fun s => (γ s)⁻¹).restrict (hV _))
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        have := fuTT_inv lam0 (fun s => (γ s)⁻¹) (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)
        simp only [inv_inv] at this
        exact this)
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact fuTT_inv lam0 γ (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf))
  refine ⟨T, fun L _ x => ?_, fun e _ x => ?_⟩
  · exact fu_Hten lam0 hDom γ _ _ (fun s => fu_extO R.ι R.σ s.val g L) _
  · exact fu_Hten lam0 hDom γ _ _ (fun s => fu_LeAt p R.ι R.σ R.w s.val g e) _

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestOIso : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (φW : R₁.W ≃+* R₂.W),
    ∃ φO : R₁.O ≃+* R₂.O, (∀ x, φO (R₁.jO x) = R₂.jO (φW x)) ∧ φO R₁.w = R₂.w

theorem restRSIso_of (hW : WittIdent) (hO : RestOIso) : RestRSIso := by
  intro p n' R₁ R₂
  have s₁ := R₁.std.1
  have s₂ := R₂.std.1
  haveI : Fact (Nat.Prime p) := ⟨s₁.prime⟩
  haveI := s₁.frac_alt
  haveI := s₂.frac_alt
  haveI := s₁.frac_O
  haveI := s₂.frac_O
  obtain ⟨φ₁, h₁⟩ := hW p n' R₁.W R₁.Qq R₁.O R₁.Kf R₁.ι R₁.σ R₁.jO R₁.w s₁
  obtain ⟨φ₂, h₂⟩ := hW p n' R₂.W R₂.Qq R₂.O R₂.Kf R₂.ι R₂.σ R₂.jO R₂.w s₂
  obtain ⟨φO, hj, hw⟩ := hO p n' R₁ R₂ (φ₁.symm.trans φ₂)
  let φQ : R₁.Qq ≃+* R₂.Qq := IsFractionRing.ringEquivOfRingEquiv (φ₁.symm.trans φ₂)
  let φK : R₁.Kf ≃+* R₂.Kf := IsFractionRing.ringEquivOfRingEquiv φO
  have hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq ((φ₁.symm.trans φ₂) x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x) :=
    fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x) := by
    have key : (φQ : R₁.Qq →+* R₂.Qq).comp (R₁.σ : R₁.Qq →+* R₁.Qq) =
        (R₂.σ : R₂.Qq →+* R₂.Qq).comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      obtain ⟨v, rfl⟩ := φ₁.surjective u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [h₁ v, hWQ, hWQ]
      simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
      rw [h₂ v]
    exact fun x => RingHom.congr_fun key x
  have hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x) := by
    have key : (φK : R₁.Kf →+* R₂.Kf).comp R₁.ι = R₂.ι.comp (φQ : R₁.Qq →+* R₂.Qq) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R₁.W)
      ext u
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [s₁.ι_comp, hOK, hj, hWQ, s₂.ι_comp]
    exact fun x => RingHom.congr_fun key x
  exact ⟨⟨φ₁.symm.trans φ₂, φQ, φO, φK, hWQ, hOK, hι, hσ, hj, hw⟩⟩

theorem lpRingIndep_of'' (hW : WittIdent) (hO : RestOIso) : LPRingIndep := lpRingIndep_of' (restRSIso_of hW hO)

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorBoundOfOrderBound
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

section Dual

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.p_zpow (z : ℤ) : (p : R.Kf) ^ z = algebraMap R.O R.Kf R.w ^ (2 * z) := by
  rw [R.p_eq, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem dual_bases (hD3 : DualHeightBasis) (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ (r : Fin (dimV R.Kf lamO) → Vsp R.Kf lamO) (ρ : Fin (dimV R.Kf lamO) → Module.Dual R.Kf (Vsp R.Kf lamO)),
      (∀ a, r a ∈ Re p R.ι R.σ R.w 1 lamO e) ∧ (∀ a, ρ a ∈ Re' p R.ι R.σ R.w 1 lamO e) ∧
      ∀ a b, be p 1 lamO (r a) (ρ b) = if a = b then 1 else 0 := by
  classical
  obtain ⟨x, π, -, -, -, -, hRe, hRe'⟩ := hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 lamO hdom e he
  refine ⟨fun a => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π a))) • x a,
    fun b => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π b)) * (p : R.Kf) ^ (-π b)) • x.coord b, ?_, ?_, ?_⟩
  · intro a
    rw [← hRe]
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [← hRe']
    exact Submodule.subset_span ⟨b, rfl⟩
  · intro a b
    unfold be
    rw [LinearMap.smul_apply, map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, smul_eq_mul, mul_one]
      rw [R.p_zpow, R.p_zpow, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne]
      have : -order 1 lamO (π a) + 2 * -π a + (2 * Ar 1 lamO + -order 1 lamO (π a)) = 0 := by
        unfold order
        ring
      rw [this, zpow_zero]
    · simp [hab]

end Dual

theorem tensor_bound_of_order_bound (hTen : RestTensor) (hOrd : RestOrdBound) (hD3 : DualHeightBasis) (hIncl : DualHeightInclusion) : ResidueClassCount := by
  classical
  intro p n' R m TT ccl aw bw lam0 hBase hDom t c₃ D κ hc hρ e he
  obtain ⟨μ, ν, hν, hHL, hHLe, hdim⟩ := hTen p n' R m TT lam0 hDom
  have hdomO : IsDominant (othW TT lam0) := othW_dom hDom
  have hsmall : ∀ s i, |othW TT lam0 s i| ≤ (ccl : ℤ) := by
    intro s i
    unfold othW
    split_ifs with hs
    · simp
    · exact (hBase s).2 hs i
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hw : wK ≠ 0 := R.w_ne
  obtain ⟨r, ρ, hr, hρm, hrρ⟩ := dual_bases R hD3 (othW TT lam0) hdomO e he
  have hA := Ar_add TT lam0

  have hsrc : ∀ F ∈ CCL R (topW TT lam0) t c₃ e, ∀ a, μ F (r a) ∈ CCL R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro F hF a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).1 (hr a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := mu_scale μ hF.1.1 hr0
      rw [← hHL e.src he.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := mu_scale μ hF.1.2 (hr a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hF' := scale_scale_mem (CCL_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hF)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).1
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := mu_scale μ hF' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have htst : ∀ G ∈ CCL' R (topW TT lam0) t c₃ e, ∀ a, ν G (ρ a) ∈ CCL' R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro G hG a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).2 (hρm a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := nu_scale μ ν hν hG.1.1 hr0
      rw [← hHL e.tgt he.2.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := nu_scale μ ν hν hG.1.2 (hρm a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hG' := scale_scale_mem (CCL'_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hG)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).2
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := nu_scale μ ν hν hG' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have hbe : ∀ F G a b, be p 1 lam0 (μ F (r a)) (ν G (ρ b)) =
      be p 1 (topW TT lam0) F G * (if a = b then 1 else 0) := by
    intro F G a b
    rw [← hrρ a b]
    unfold be
    have hp0 : (p : R.Kf) ≠ 0 := by rw [R.p_eq]; exact pow_ne_zero _ hw
    rw [map_smul, hν, map_smul, map_smul, hA, zpow_add₀ hp0]
    simp only [smul_eq_mul]
    ring
  obtain ⟨nT, hnT, hfac⟩ := hρ e he
  refine ⟨nT * (dimV R.Kf (othW TT lam0)), ?_, ?_⟩
  · have h1 : dL R lam0 = dL R (topW TT lam0) * (dimV R.Kf (othW TT lam0)) := by
      unfold dL
      rw [hdim]
      push_cast
      ring
    rw [h1, ← mul_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right hnT (Nat.cast_nonneg _)
  · rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
    · exact Or.inl (by rw [h0, zero_mul])
    · refine FactorsLE_of_index (I := Fin nT × Fin (dimV R.Kf (othW TT lam0))) (nT * (dimV R.Kf (othW TT lam0))) (by simp)
        (fun i => μ (x i.1) (r i.2)) (fun l => ν (y l.1) (ρ l.2)) (fun i => hsrc _ (hx i.1) i.2)
        (fun l => htst _ (hy l.1) l.2) z (Matrix.of fun l j => if l.2 = j.2 then M l.1 j.1 else 0) hz hv ?_
      rintro ⟨i, a⟩ ⟨j, b⟩
      rw [Fintype.sum_prod_type]
      simp only [hbe, Matrix.of_apply]
      have h2 : ∀ l : Fin nT, ∑ b' : Fin (dimV R.Kf (othW TT lam0)), be p 1 (topW TT lam0) (x i) (y l) * (if a = b' then 1 else 0) *
          algebraMap R.O R.Kf (if b' = b then M l j else 0) =
          if a = b then be p 1 (topW TT lam0) (x i) (y l) * algebraMap R.O R.Kf (M l j) else 0 := by
        intro l
        rw [Finset.sum_eq_single a]
        · by_cases hab : a = b <;> simp [hab]
        · intro b' _ hb'
          simp [Ne.symm hb']
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h2]
      by_cases hab : a = b
      · subst hab
        simp only [if_true]
        rw [hM i j]
        by_cases hij : i = j
        · subst hij; simp
        · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, a) := fun h => hij (Prod.mk.inj h).1
          rw [if_neg hij, if_neg this]
      · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, b) := fun h => hab (Prod.mk.inj h).2
        simp [hab, this]

end Formalism.MainNotions.flipOneThree.Pf

end
end

