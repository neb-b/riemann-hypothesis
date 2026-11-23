module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
section
noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

def form6 (O : Type) [CommRing O] : FormData O wt6 where
  J := Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0
  unit := IsUnit.of_mul_eq_one (Matrix.fromBlocks 0 (Jmat O 3) (Jmat O 3) 0) (by
    simp [Matrix.fromBlocks_multiply, Jmat_mul_Jmat])
  sym := Or.inl (by simp [Matrix.fromBlocks_transpose, Jmat_transpose])
  κ := Bool
  blk := Sum.isLeft
  σ := not
  invol := Bool.not_not
  hblk a b h := by
    rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢
  c := 0
  hw a b h := by
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [Jmat] at h <;> first | rfl | exact absurd rfl h

theorem blockPairingForm_JR (O R : Type) [CommRing O] [CommRing R] [Algebra O R] :
    (form6 O).JR R = Matrix.fromBlocks 0 (Jmat R 3) (Jmat R 3) 0 := by
  simp [FormData.JR, form6, Matrix.fromBlocks_map, Jmat_map]

theorem emb_apply {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) :
    emb x = if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
      else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0 := rfl

theorem emb_map' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : GG (m := m) (R := R)) :
    emb (GG.map f x) = (emb x).map f := by
  have h : (theta (GG.map f x).left : Matrix (Fin m) (Fin m) S) = (theta x.left : Matrix (Fin m) (Fin m) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  rw [emb_apply, emb_apply, h, GG.map_mat, GG.map_right]
  split_ifs <;> simp [Matrix.fromBlocks_map]

theorem mat_eq_emb' {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) (a b : Fin m) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  rw [emb_apply]
  split_ifs <;> simp

theorem eq_of_emb {m : ℕ} {R : Type*} [CommRing R] {x y : GG (m := m) (R := R)}
    (h : x.right = y.right) (e : emb x = emb y) :
    x = y := by
  refine SemidirectProduct.ext (Units.ext ?_) h
  ext a b
  exact (mat_eq_emb' x a b).trans (e ▸ (mat_eq_emb' y a b).symm)

theorem emb_form (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] (x : GG (m := 3) (R := R)) :
    (emb x)ᵀ * (form6 O).JR R * emb x = (form6 O).JR R := by
  have h1 : x.matᵀ * Jmat R 3 * (theta x.left : GL (Fin 3) R) = Jmat R 3 := by
    rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3), Jmat_mul_Jmat,
      Matrix.mul_one, GG.mat, ← Matrix.transpose_mul]
    simp
  have h2 : ((theta x.left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 * x.mat = Jmat R 3 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose,
      ← Matrix.mul_assoc] at this
  rw [blockPairingForm_JR, emb_apply]
  split_ifs <;> simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h1, h2]

theorem emb_blk {m : ℕ} {R : Type*} [CommRing R] (x : GG (m := m) (R := R)) (a b : Fin m ⊕ Fin m)
    (h : emb x a b ≠ 0) :
    a.isLeft = if x.right = 1 then b.isLeft else !b.isLeft := by
  rw [emb_apply] at h
  split_ifs at h ⊢ <;> rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢

theorem unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  rw [emb_apply, GG.mat, unitaryThreeReflection_left, theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

def sgnPerm : ℤˣ →* Equiv.Perm Bool where
  toFun s := if s = 1 then 1 else Function.Involutive.toPerm not Bool.not_not
  map_one' := if_pos rfl
  map_mul' s t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;> decide

theorem blockPairingForm_normalises_baseLift (O : Type) [CommRing O] {G R : Type} [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (form6 O).Normalises (emb.comp (r0 η Ψ)) := by
  refine ⟨fun g => ⟨1, by rw [one_smul]; exact emb_form O _⟩, ⟨sgnPerm.comp η, fun g a b h => ?_⟩,
    fun g a b h => unitaryGroupEmbedding_baseLift_eq_zero_of_wt_ne η Ψ g a b h⟩
  have := emb_blk _ a b h
  show a.isLeft = (if η g = 1 then 1 else Function.Involutive.toPerm not Bool.not_not : Equiv.Perm Bool) b.isLeft
  rw [this, unitaryThreeReflection_right]
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ}
  {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

theorem baseLift_map_residue {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (g : G) :
    GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

theorem GLift.locConst (hη : IsLocallyConstant η) (r : GLift O η Ψ R) (n : ℕ) :
    IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (r.hom g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hη x
  have h2 : ∀ᶠ y in nhds x, ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom y).mat a b) =
      Ideal.Quotient.mk (maximalIdeal R ^ n) ((r.hom x).mat a b) :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (r.cont a b n) x
  filter_upwards [h1, h2] with y e1 e2
  refine SemidirectProduct.ext (Units.ext ?_) ((r.hasMult y).trans (e1.trans (r.hasMult x).symm))
  ext a b
  exact e2 a b

def GLift.toLift (hη : IsLocallyConstant η) (r : GLift O η Ψ R) : Lift O (emb.comp (rbar O η Ψ)) R where
  hom := emb.comp r.hom
  cont a b n := by
    have := (r.locConst hη n).comp fun x => emb x a b
    simpa only [Function.comp_def, emb_map', Matrix.map_apply, MonoidHom.comp_apply] using this
  red g a b := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← r.red g, emb_map']
    rfl

abbrev unitFrame {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (π : G →* Γ)
    (hπ : Continuous π) (ι : H →* G) (hι : Continuous ι) {Q : Type} [Fintype Q] (D : Q → Subgroup G)
    (N : Q → Subgroup G) : Frame Γ where
  T := Unit
  v0 := ()
  Gv _ := H
  φ _ := π.comp ι
  hφ _ := hπ.comp hι
  Q := Q
  Gq q := D q
  ψ q := π.comp (D q).subtype
  hψ _ := hπ.comp continuous_subtype_val
  N q := (N q).subgroupOf (D q)

abbrev adBar (O : Type) [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (j : ℤ) :
    Representation (ResidueField O) G ((form6 O).gw (ResidueField O) j) :=
  FormData.adRep (ρ := emb.comp (rbar O η Ψ)) (blockPairingForm_normalises_baseLift O η (barChar O Ψ)) j

end UpperTheory.V.U3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GradedModelDerivationConditionOfPtHyp
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem exists_twist (t : Kˣ) (D : A →ₗ[O] K) :
    ∃ E : A →ₗ[O] K, ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a := by
  classical
  refine ⟨(DirectSum.toModule O ℤ K (fun j => ((t ^ j : Kˣ) : K) • (D ∘ₗ (𝒜 j).subtype))) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap, ?_⟩
  intro j a ha
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem 𝒜 ha]
  rw [← DirectSum.lof_eq_of O, DirectSum.toModule_lof]
  simp [smul_eq_mul]

private theorem act_tz (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {a : A} (ha : a ∈ 𝒜 j) :
    act 𝒜 (tz t) ξ a = ((t ^ j : Kˣ) : K) * ξ a := act_of_mem 𝒜 _ ξ ha

private theorem twist_der (t : Kˣ) (ξ : A →ₐ[O] K) (D E : A →ₗ[O] K) (hD : D ∈ PtDer ξ K)
    (hE : ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a) : E ∈ PtDer (act 𝒜 (tz t) ξ) K := by
  have hD' : ∀ f g : A, D (f * g) = ξ f • D g + ξ g • D f := hD
  show ∀ f g : A, E (f * g) = act 𝒜 (tz t) ξ f • E g + act 𝒜 (tz t) ξ g • E f
  intro f g
  refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun f => E (f * g) = act 𝒜 (tz t) ξ f • E g + act 𝒜 (tz t) ξ g • E f) ?_ ?_ ?_ f
  · simp
  · intro i a
    refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun g => E (a * g) = act 𝒜 (tz t) ξ a • E g + act 𝒜 (tz t) ξ g • E a) ?_ ?_ ?_ g
    · simp
    · intro j b
      have hab : (a : A) * b ∈ 𝒜 (i + j) := SetLike.GradedMul.mul_mem a.2 b.2
      rw [hE _ _ hab, hE _ _ b.2, hE _ _ a.2, act_tz 𝒜 t ξ a.2, act_tz 𝒜 t ξ b.2, hD', _root_.zpow_add, Units.val_mul]
      simp only [smul_eq_mul]
      ring
    · intro g g' h h'
      simp only [mul_add, map_add (f := _), smul_add, add_smul, smul_eq_mul] at h h' ⊢
      rw [h, h']
      ring
  · intro f f' h h'
    simp only [add_mul, map_add (f := _), smul_add, add_smul, smul_eq_mul] at h h' ⊢
    rw [h, h']
    ring

omit [GradedAlgebra 𝒜] in
private theorem twist_kills {x : A →ₐ[O] O} {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) (t : Kˣ)
    (ξ : A →ₐ[O] K) (D E : A →ₗ[O] K) (hξ : OnS Q.ideal ξ) (hE' : E ∈ PtDer ξ K)
    (hE : ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a) (hD : ∀ y ∈ Q.ideal, D y = 0) :
    ∀ y ∈ Q.ideal, E y = 0 := by
  intro y hy
  have hξ' : ∀ f ∈ Q.ideal, ξ f = 0 := hξ
  have hE'' : ∀ f g : A, E (f * g) = ξ f • E g + ξ g • E f := hE'
  have hgen : ∀ z ∈ (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z), E z = 0 := by
    intro z hz
    have hzI : z ∈ Q.ideal := Ideal.subset_span hz
    obtain ⟨j, hj⟩ : ∃ j, z ∈ 𝒜 j := by
      rcases hz with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
    rw [hE j z hj, hD z hzI, mul_zero]
  have hy' : y ∈ Submodule.span A (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz => exact hgen z hz
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b hb hb0 =>
    rw [smul_eq_mul, hE'', hb0, hξ' b hb]
    simp

private theorem cob_smul {G C : Type} [Group G] [CommRing C] {m : ℕ} (r : G →* GG (m := m) (R := C)) (a : C)
    (X : Matrix (Fin m) (Fin m) C) : cob r (a • X) = a • cob r X := by
  funext g
  simp only [cob, map_smul, Pi.smul_apply, smul_sub]

private theorem zmat_map {G R R' : Type} [Group G] [CommRing R] [CommRing R'] (f : R →+* R')
    (r : G →* GG (m := 3) (R := R))
    (c g₁ : G) (a b : Fin 3) : zmat c g₁ ((GG.map f).comp r) a b = f (zmat c g₁ r a b) := by
  simp [zmat]

private theorem normalised_map {G R R' : Type} [Group G] [CommRing R] [CommRing R'] (f : R →+* R')
    (r : G →* GG (m := 3) (R := R)) (c g₁ : G) (h : Normalised c g₁ r) :
    Normalised c g₁ ((GG.map f).comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [GG.map_mat, h.atc]
  · rw [zmat_map, h.z12, map_zero]
  · rw [zmat_map, h.z21, map_zero]

private theorem isUnit_zeta {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R)
    {c g₁ : Γ} (h : Marks η Ψ c g₁) : IsUnit (zeta c g₁ r.hom) := by
  have hm : Marks η (barChar O Ψ) c g₁ := by
    refine ⟨h.csq, h.ηc, by simp [barChar, h.Ψc], h.ηg, ?_⟩
    have := h.Ψg.map (residue O)
    rw [map_sub, map_pow, map_one] at this
    exact this
  have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit η (barChar O Ψ) c g₁ hm).2
  have h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ) :=
    MonoidHom.ext r.red
  rw [← h2, zeta, zmat_map] at h1
  by_contra hn
  have h3 : res O R (zeta c g₁ r.hom) = 0 := (res_eq_zero_iff O R _).2 hn
  exact h1.ne_zero h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.gradedModel_derivationCondition_of_ptHyp :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → PtHyp η S.r.hom M.x₀ → M4 M.𝒜 (PadicAlgCl l) M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm hM2 hpt
  intro ξ hξ hsign D hD D' hD' hDI hD'I
  obtain ⟨t, f, hf, hact⟩ := M.pts hM2 ξ hξ
  obtain ⟨E, hE⟩ := exists_twist M.𝒜 t D
  obtain ⟨E', hE'⟩ := exists_twist M.𝒜 t D'
  have hEd : E ∈ PtDer (f.comp M.q) (PadicAlgCl l) := hact ▸ twist_der M.𝒜 t ξ D E hD hE
  have hE'd : E' ∈ PtDer (f.comp M.q) (PadicAlgCl l) := hact ▸ twist_der M.𝒜 t ξ D' E' hD' hE'
  have hon : OnS M.Q.ideal (f.comp M.q) := by
    intro y hy
    have : M.q y = 0 := by
      rw [← RingHom.mem_ker, M.ker_q]
      exact hy
    simp [this]
  have hEI : ∀ y ∈ M.Q.ideal, E y = 0 := twist_kills M.𝒜 M.Q t (f.comp M.q) D E hon hEd hE hDI
  have hE'I : ∀ y ∈ M.Q.ideal, E' y = 0 := twist_kills M.𝒜 M.Q t (f.comp M.q) D' E' hon hE'd hE' hD'I
  obtain ⟨F, hF, hFE⟩ := M.der hM2 f hf E hEd hEI
  obtain ⟨F', hF', hFE'⟩ := M.der hM2 f hf E' hE'd hE'I
  have htne : ∀ j : ℤ, ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) ≠ 0 := fun j => Units.ne_zero _
  have hneg : NegZero M.𝒜 (f.comp M.q) ↔ NegZero M.𝒜 ξ := by
    rw [← hact]
    constructor
    · intro h j hj y hy
      have := h j hj y hy
      rw [act_tz M.𝒜 t ξ hy] at this
      exact (mul_eq_zero.1 this).resolve_left (htne j)
    · intro h j hj y hy
      rw [act_tz M.𝒜 t ξ hy, h j hj y hy, mul_zero]
  have hpos : PosZero M.𝒜 (f.comp M.q) ↔ PosZero M.𝒜 ξ := by
    rw [← hact]
    constructor
    · intro h j hj y hy
      have := h j hj y hy
      rw [act_tz M.𝒜 t ξ hy] at this
      exact (mul_eq_zero.1 this).resolve_left (htne j)
    · intro h j hj y hy
      rw [act_tz M.𝒜 t ξ hy, h j hj y hy, mul_zero]
  have hsg := model_signs S M hl hm f hf
  have htwo : TwoPt (η := η) S.r.hom f :=
    ⟨hf, fun h => hsign.1 (hneg.1 (hsg.1.2 h)), fun h => hsign.2 (hpos.1 (hsg.2.1.2 h))⟩
  have hrig := hpt.rigid f htwo
  obtain ⟨X, hX⟩ := hrig F hF
  obtain ⟨X', hX'⟩ := hrig F' hF'
  have hN0 := ((S.rep S.R).1 (AlgHom.id _ _)).1
  have hN : Normalised cc g₁ S.r.hom := by
    refine ⟨?_, ?_, ?_⟩
    · have := hN0.atc
      simpa [GLift.map, GG.map_mat] using this
    · have := hN0.z12
      simp only [GLift.map] at this
      rw [zmat_map ((AlgHom.id c.O S.R : S.R →ₐ[c.O] S.R) : S.R →+* S.R)] at this
      simpa using this
    · have := hN0.z21
      simp only [GLift.map] at this
      rw [zmat_map ((AlgHom.id c.O S.R : S.R →ₐ[c.O] S.R) : S.R →+* S.R)] at this
      simpa using this
  have hright : ∀ g, (S.r.hom g).right = η g := by
    intro g
    have := congrArg SemidirectProduct.right (S.r.red g)
    simpa [GG.map, SemidirectProduct.map_right, rbar, r0] using this
  have hc : (push f S.r.hom cc).right = -1 := by
    simp [push, GG.map, SemidirectProduct.map_right, hright, hm.ηc]
  have hg : (push f S.r.hom g₁).right = 1 := by
    simp [push, GG.map, SemidirectProduct.map_right, hright, hm.ηg]
  have hPN : Normalised cc g₁ (push f S.r.hom) := normalised_map (f : S.R →+* PadicAlgCl l) S.r.hom cc g₁ hN
  have hz : IsUnit (zeta cc g₁ (push f S.r.hom)) := by
    have := (isUnit_zeta S.r hm).map (f : S.R →+* PadicAlgCl l)
    simpa [zeta, push, zmat_map] using this
  have h2 : IsUnit (2 : PadicAlgCl l) := isUnit_iff_ne_zero.2 two_ne_zero
  have hdet := tanCoc_determines S M hl hm F (hF ▸ hf)
  have hdet' := tanCoc_determines S M hl hm F' (hF' ▸ hf)
  have hXm : X ∈ unitaryThreeTorusLieAlgebra (PadicAlgCl l) := by
    have := hdet.2.1
    rw [hF, hX] at this
    exact (normCoc_cob_iff _ cc g₁ X h2 hc hg hPN hz).1 this
  have hX'm : X' ∈ unitaryThreeTorusLieAlgebra (PadicAlgCl l) := by
    have := hdet'.2.1
    rw [hF', hX'] at this
    exact (normCoc_cob_iff _ cc g₁ X' h2 hc hg hPN hz).1 this
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hXm
  obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.1 hX'm
  obtain ⟨a, a', hne, hrel⟩ : ∃ a a' : PadicAlgCl l, (a ≠ 0 ∨ a' ≠ 0) ∧
      a • tanCoc F S.r.hom + a' • tanCoc F' S.r.hom = 0 := by
    rw [hX, hX', cob_smul, cob_smul]
    by_cases hx' : x' = 0
    · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
      simp [hx']
    · refine ⟨x', -x, Or.inl hx', ?_⟩
      funext g
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_smul]
      rw [← add_smul]
      have : x' * x + -x * x' = 0 := by ring
      rw [this, zero_smul]
  have hall := hdet.2.2.2.2 F' (by rw [hF, hF']) a a' hrel
  have hEE : ∀ y : M.A, a * E y + a' * E' y = 0 := by
    intro y
    rw [← hFE y, ← hFE' y]
    exact hall (M.q y)
  refine ⟨a, a', hne, ?_⟩
  apply LinearMap.ext
  intro y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
  refine DirectSum.Decomposition.inductionOn M.𝒜 (motive := fun y => a * D y + a' * D' y = 0) ?_ ?_ ?_ y
  · simp
  · intro j z
    have h := hEE z
    rw [hE j z z.2, hE' j z z.2] at h
    have h' : ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (a * D z + a' * D' z) = 0 := by
      rw [← h]
      ring
    exact (mul_eq_zero.1 h').resolve_left (htne j)
  · intro y y' h h'
    simp only [map_add (f := _)]
    linear_combination h + h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GradedModelPointConditionOfPtHyp
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  classical
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have key := UpperTheory.V.Base.normO l c.O b h0
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb ((IsDiscreteValuationRing.addVal_eq_zero_iff).1 h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).1 h)
  have hn : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hn
  rw [← key] at hr
  by_cases he : (UpperTheory.V.Base.eO l c.O).toNat = 0
  · rw [he, pow_zero] at hr
    exact absurd hr (lt_irrefl 1)
  · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 hr

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem hom_ext_gr {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] [CommRing K] [Algebra O K] (ξ ξ' : A →ₐ[O] K) (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  refine AlgHom.ext fun f => ?_
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => exact h _ _ m.2
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem UpperTheory.V.U3.gradedModel_pointCondition_of_ptHyp :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → PtHyp η S.r.hom M.x₀ → M3 M.𝒜 (PadicAlgCl l) M.x M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm h2 hpt
  intro x₁ hS hN hP hne
  exfalso
  apply hne
  obtain ⟨t, f, hf, hact⟩ := M.pts h2 x₁ hS
  have sg := model_signs S M hl hm f hf
  have hN' : NegZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hN j hj a ha, mul_zero]
  have hP' : PosZero M.𝒜 (f.comp M.q) := by
    intro j hj a ha
    rw [← hact, act_of_mem _ _ _ ha, hP j hj a ha, mul_zero]
  have hfix := hpt.fixed f hf (sg.1.1 hN') (sg.2.1.1 hP')
  have hb : IsLocPt (toBar M.x₀) := isLocPt_toBar M.x₀
  have hconj : push (toBar M.x₀) S.r.hom = conjBy ((tor (PadicAlgCl l)) 1) (push f S.r.hom) := by
    rw [hfix]
    ext g : 1
    simp [conjBy]
  have heq := sg.2.2 (toBar M.x₀) hb 1 hconj
  apply hom_ext_gr M.𝒜
  intro j a ha
  by_cases hj : j = 0
  · subst hj
    have e1 := congrArg (fun φ => φ a) hact
    have e2 := congrArg (fun φ => φ a) heq
    simp only [act_of_mem _ _ _ ha] at e1 e2
    simp at e1 e2
    rw [← M.x₀_q]
    simp
    rw [e1, e2]
  · rcases lt_or_gt_of_ne hj with h | h
    · rw [hN j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
    · rw [hP j h a ha, AlgHom.comp_apply, M.wring.fixed j hj a ha, map_zero]
end

