module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TorStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsLiftD
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open UpperTheory.V.UnitaryThreeInertia.TorStep

variable {O A D : Type} [CommRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group D]

private theorem psi_diff (Ψ : D →* Oˣ) (x : D) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) :
    IsUnit (psi Ψ a x - psi Ψ b x) := by
  have h0 : psi Ψ 0 x = (Ψ x : O) := by simp [psi, wt1]
  have h1 : psi Ψ 1 x = 1 := by simp [psi, wt1]
  have h2 : psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [psi, wt1]
  have hi : (Ψ x : O) * ((Ψ x)⁻¹ : Oˣ) = 1 := Units.mul_inv _
  have e01 : IsUnit (psi Ψ 0 x - psi Ψ 1 x) := by
    rw [h0, h1]
    exact isUnit_of_mul_isUnit_left (y := (Ψ x : O) + 1) (by convert hx using 1; ring)
  have e12 : IsUnit (psi Ψ 1 x - psi Ψ 2 x) := by
    rw [h0, h1] at e01
    rw [h1, h2]
    convert e01.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -hi
  have e02 : IsUnit (psi Ψ 0 x - psi Ψ 2 x) := by
    rw [h0, h2]
    convert hx.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -(Ψ x : O) * hi
  have neg : ∀ {u w : O}, IsUnit (u - w) → IsUnit (w - u) := fun h => by rw [← neg_sub]; exact h.neg
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | (apply neg; assumption)

private theorem unit_of_res {y : A} {u : O} (hu : IsUnit u) (h : residue A y = residue A (algebraMap O A u)) :
    IsUnit y := by
  rw [← residue_ne_zero_iff_isUnit, h, residue_ne_zero_iff_isUnit]
  exact hu.map _

private theorem res_left [IsLocalRing O] {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG (m := 3) (R := A)} (hr : Red η Ψ r) (g : D) :
    GeneralLinearGroup.map (residue A) (r g).left = GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)) := by
  apply Units.ext
  ext a b
  have h := (residue_eq_zero_iff _).2 (hr.red g a b)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  have h2 : GeneralLinearGroup.map (algebraMap O A) (tor O (Ψ g)) = tor A (chr Ψ A g) := map_tor _ _
  rw [← h2]
  exact h

private theorem res_conj {h : GL (Fin 3) A} (hh : InHat h) (r : D →* GG (m := 3) (R := A)) (g : D) :
    GeneralLinearGroup.map (residue A) (conjBy h⁻¹ r g).left = GeneralLinearGroup.map (residue A) (r g).left := by
  have h1 : GG.map (residue A) (GG.ofGL h) = 1 := by
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    ext a b
    have h := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    show _ = (1 : Matrix (Fin 3) (Fin 3) _) a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : GG.map (residue A) (conjBy h⁻¹ r g) = GG.map (residue A) (r g) := by
    show GG.map (residue A) (GG.ofGL h⁻¹ * r g * (GG.ofGL h⁻¹)⁻¹) = _
    simp only [map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  exact congrArg SemidirectProduct.left h2

private theorem diag_all [Finite A] {η : D →* ℤˣ} {Ψ : D →* Oˣ} (t : D →* GG (m := 3) (R := A)) (hm : HasMult η t)
    (hres : ∀ g, GeneralLinearGroup.map (residue A) (t g).left =
      GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)))
    (hd : ∀ g, η g = 1 → (t g).mat.IsDiag) (x : D) (hηx : η x = 1) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (g : D) :
    (t g).mat.IsDiag := by
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hd g hg
  have hη2 : η (g * x * g⁻¹) = 1 := by rw [map_mul, map_mul, hηx, mul_one, map_inv, mul_inv_cancel]
  have hΨ2 : chr Ψ A (g * x * g⁻¹) = chr Ψ A x := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have e : t (g * x * g⁻¹) * t g = t g * t x := by rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have e1 : (t (g * x * g⁻¹)).mat * (t g).mat = (t g).mat * (theta (t x).left).val := by
    have := congrArg (fun z : GG (m := 3) (R := A) => z.left.val) e
    simpa only [GG.mat, SemidirectProduct.mul_left, hm _, hη2, hg, sgnAct_one, sgnAct_neg_one, Units.val_mul] using this
  have d1 := hd _ hη2
  have d2 : (theta (t x).left).val.IsDiag := by
    intro a b hab
    rw [theta_apply]
    exact isDiag_inv (hd x hηx) fun e => hab (Fin.rev_injective e).symm
  have r1 : ∀ a, residue A ((t (g * x * g⁻¹)).mat a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) (hres (g * x * g⁻¹))
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [hΨ2, tor_chr_apply, Matrix.diagonal_apply_eq]
  have r2 : ∀ a, residue A ((theta (t x).left).val a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have h3 : GeneralLinearGroup.map (residue A) (theta (t x).left) =
        GeneralLinearGroup.map (residue A) (tor A (chr Ψ A x)) := by
      rw [map_theta, hres, ← map_theta, theta_tor]
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) h3
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [tor_chr_apply, Matrix.diagonal_apply_eq]
  intro a b hab
  have hu : IsUnit ((t (g * x * g⁻¹)).mat a a - (theta (t x).left).val b b) :=
    unit_of_res (psi_diff Ψ x hx a b hab) (by rw [map_sub, map_sub, map_sub, r1, r2])
  have e2 := congrFun (congrFun e1 a) b
  rw [← d1.diagonal_diag, ← d2.diagonal_diag, Matrix.diagonal_mul, Matrix.mul_diagonal] at e2
  apply hu.mul_left_cancel
  simp only [Matrix.diag_apply] at e2
  linear_combination e2

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_lift_d :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v ∈ F.Sb → ∀ (r' : F.D v →* GG (m := 3) (R := R')), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG (m := 3) (R := R), push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R R' _ _ _ _ _ _ 𝒜 _ p j hp hS v hv r' hred hloc hlc hgr
  haveI : Finite R := hS.fin
  haveI : Finite R' := Finite.of_surjective p hp
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hvT : v ∈ F.Tb := Set.mem_insert_of_mem _ hv
  have hcont : Continuous (F.loc v) := hF.π_cont.comp continuous_subtype_val
  obtain ⟨x, hηx, hx⟩ := hF.x v hvT
  obtain ⟨φ, hφ, hd⟩ := hF.frob v
  obtain ⟨X, hXg, hX⟩ := hgr x
  have hXp : ∀ a b, (p : R →+* R') (X a b) = (r' x).mat a b := fun a b => congrFun (congrFun hX a) b
  have hrx : ∀ a b, residue R' ((r' x).mat a b) =
      residue R' (diagonal (fun a => algebraMap O R' (psi (F.Ψv v) a x)) a b) := fun a b => by
    rw [← TorStep.tor_chr_apply]
    exact congrArg (fun z : GL (Fin 3) _ => z.val a b) (res_left hred x)
  have hXu : ∀ a b, a ≠ b → IsUnit (X a a - X b b) := fun a b hab => by
    apply IsUnit.of_map (p : R →+* R')
    refine unit_of_res (psi_diff _ x hx a b hab) ?_
    rw [map_sub, map_sub, map_sub, map_sub, hXp, hXp, hrx, hrx, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  have hXm : ∀ a b, a ≠ b → X a b ∈ maximalIdeal R := fun a b hab hu => by
    have h1 := hu.map (p : R →+* R')
    rw [hXp, ← residue_ne_zero_iff_isUnit, hrx, Matrix.diagonal_apply_ne _ hab, map_zero] at h1
    exact h1 rfl
  obtain ⟨h, hh⟩ := exists_canon X hXu hXm
  obtain ⟨hg1, hg2⟩ := canon_graded 𝒜 X h hXu hXg hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  rw [show X.map (p : R →+* R') = (r' x).mat from hX] at hh'
  set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'def
  have hD : DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) r' h' :=
    (cond_iff_canon _ _ _ r' x h' hred hηx hx hh').2.1 (hloc.2.1 hv)
  have hconj : ∀ {A : Type} [CommRing A] (k : GL (Fin 3) A) (r : F.D v →* GG (m := 3) (R := A)) (g : F.D v),
      conjBy k r g = GG.ofGL k * r g * GG.ofGL k⁻¹ := fun k r g => by rw [map_inv]; rfl
  have hmap : ∀ k : GL (Fin 3) R, GG.map (p : R →+* R') (GG.ofGL k) =
      GG.ofGL (GeneralLinearGroup.map (p : R →+* R') k) := fun k => rfl
  have hm : HasMult (F.ηv v) (conjBy h'⁻¹ r') := fun g => by
    rw [hconj]
    simp [hred.mult g]
  have hdiag : ∀ g, (conjBy h'⁻¹ r' g).mat.IsDiag := by
    refine diag_all (Ψ := F.Ψv v) _ hm (fun g => (res_conj hh'.hat r' g).trans (res_left hred g)) ?_ x hηx hx
    intro g hg a b hab
    rcases lt_trichotomy (wt a b) 0 with h0 | h0 | h0
    · exact hD.tri g hg a b h0
    · exact absurd (Fin.ext (by unfold wt wt1 at h0; omega)) hab
    · exact hD.low g hg a b h0
  have hlc' : IsLocallyConstant r' :=
    TorStep.isLocallyConstant_GG (F.ηv v) (hF.η_cont.comp_continuous hcont) r' hred.mult hlc
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5⟩ := TorStep.exists_torus_lift 𝒜 p (F.Iv v) φ hφ hd (F.Ψv v)
    (fun n => (hF.Ψ_cont n).comp_continuous hcont) (conjBy h'⁻¹ r')
    (hlc'.comp (MulAut.conj (GG.ofGL h'⁻¹))) hdiag
    (fun s hs => by
      refine SemidirectProduct.ext (Units.ext ?_) ((hm s).trans (hF.η_I v hvT s hs))
      show (conjBy h'⁻¹ r' s).mat = (tor R' _).val
      rw [TorStep.tor_chr_apply, ← (hdiag s).diagonal_diag]
      congr 1
      funext a
      exact hD.ine s hs (hF.η_I v hvT s hs) a)
    (fun a => by
      obtain ⟨W, hW1, hW2⟩ := hgr φ
      have hWu : IsUnit W := by
        rw [Matrix.isUnit_iff_isUnit_det]
        apply IsUnit.of_map (p : R →+* R')
        rw [RingHom.map_det, RingHom.mapMatrix_apply, show W.map (p : R →+* R') = (r' φ).mat from hW2]
        exact (Matrix.isUnit_iff_isUnit_det _).1 (r' φ).left.isUnit
      obtain ⟨W, rfl⟩ := hWu
      let w : GG (m := 3) (R := R) := ⟨W, (r' φ).right⟩
      have hw : GG.map (p : R →+* R') w = r' φ := SemidirectProduct.ext (Units.ext hW2) rfl
      have h1 : GrMat 𝒜 (GG.ofGL h⁻¹ * w * GG.ofGL h).mat :=
        TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg2 hW1) hg1
      have h2 : GG.map (p : R →+* R') (GG.ofGL h⁻¹ * w * GG.ofGL h) = conjBy h'⁻¹ r' φ := by
        rw [hconj, map_mul, map_mul, hw, hmap, hmap, map_inv, inv_inv]
      refine ⟨(GG.ofGL h⁻¹ * w * GG.ofGL h).mat a a, ?_, ?_⟩
      · have := h1 a a
        rwa [show wt a a = 0 from sub_self _] at this
      · rw [← h2]; rfl)
  have hback : conjBy h⁻¹ (conjBy h t) = t := MonoidHom.ext fun g => by
    rw [hconj, hconj, inv_inv, map_inv]; group
  refine ⟨conjBy h t, MonoidHom.ext fun g => ?_, ⟨fun e => absurd (e ▸ hv) hF.vl_notMem, fun _ => ⟨h, hh.hat, ?_⟩,
    fun e => absurd hvT e⟩, (ht2.comp (MulAut.conj (GG.ofGL h))).comp GG.mat, fun g => ?_⟩
  · show GG.map _ (conjBy h t g) = r' g
    have : GG.map (p : R →+* R') (t g) = conjBy h'⁻¹ r' g := DFunLike.congr_fun ht1 g
    rw [hconj, map_mul, map_mul, this, hconj, hmap, hmap]
    simp only [map_inv, ← hh'def]
    group
  · refine ⟨⟨fun g _ a b h0 => ?_, fun s hs _ a => ?_⟩, fun g _ a b h0 => ?_⟩
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
    · rw [hback, ht4 s hs]
      show (tor R _).val a a = _
      rw [TorStep.tor_chr_apply, Matrix.diagonal_apply_eq]
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
  · rw [hconj]
    exact TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg1 (ht5 g)) hg2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtBasis
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lb_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((t : O) - 1) := by
    have : (t : O) ^ 2 - 1 = ((t : O) - 1) * ((t : O) + 1) := by ring
    rw [this] at ht
    exact isUnit_of_mul_isUnit_left ht
  have hi : ((t⁻¹ : Oˣ) : O) * (t : O) = 1 := by simp
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have : (t : O) - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) ^ 2 - 1) := by
      linear_combination (-(t : O)) * hi
    rw [this]
    exact (Units.isUnit _).mul ht
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have : 1 - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) - 1) := by
      linear_combination (-1 : O) * hi
    rw [this]
    exact (Units.isUnit _).mul h1
  fin_cases a <;> fin_cases b <;> simp [wt1] at hab ⊢
  all_goals first
    | exact h1 | exact h2 | exact h3
    | exact (by simpa [neg_sub] using h1.neg)
    | exact (by simpa [neg_sub] using h2.neg)
    | exact (by simpa [neg_sub] using h3.neg)

theorem UpperTheory.V.UnitaryThreeInertia.lt_basis :
    ∀ {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R'), Function.Surjective p →
      ∀ (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r' : D →* GG (m := 3) (R := R')) (x : D), Red η Ψ r' → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → CondT η Ψ I r' →
      (∃ X, GrMat 𝒜 X ∧ X.map p = (r' x).mat) →
      ∃ h : GL (Fin 3) R, InHat h ∧ GrMat 𝒜 h.val ∧ InHat (GeneralLinearGroup.map (p : R →+* R') h) ∧ TriIn η Ψ I r' (GeneralLinearGroup.map (p : R →+* R') h) := by
  intro O R R' D _ _ _ _ _ _ _ _ _ _ 𝒜 _ p hp η Ψ I r' x hr hx hΨ hc hex
  obtain ⟨X, hX, hXp⟩ := hex
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hm : ∀ y : R, p y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
    intro y
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (p : R →+* R') y)
  have hd : (r0 η Ψ x).mat = diagonal fun i => (((Ψ x) ^ wt1 i : Oˣ) : O) := by
    unfold GG.mat
    rw [unitaryThreeReflection_left, tor_val]
  have hred := hr.red x
  rw [hd] at hred
  have hent : ∀ a b : Fin 3, p (X a b) = (r' x).mat a b := by
    intro a b
    rw [← hXp]
    rfl
  have hoff : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R := by
    intro a b hab
    rw [← hm, hent]
    have := hred a b
    simpa [Matrix.map_apply, Matrix.diagonal_apply_ne _ hab] using this
  have hdiff : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b) := by
    intro a b hab
    by_contra hn
    have h1 : X a a - X b b ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    rw [← hm, map_sub, hent, hent] at h1
    have ha := hred a a
    have hb := hred b b
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at ha hb
    have hu : IsUnit (algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O))) :=
      (lb_unit (Ψ x) hΨ a b hab).map _
    apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
    have : algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O)) =
        ((r' x).mat a a - (r' x).mat b b) - ((r' x).mat a a - algebraMap O R' (((Ψ x) ^ wt1 a : Oˣ) : O))
          + ((r' x).mat b b - algebraMap O R' (((Ψ x) ^ wt1 b : Oˣ) : O)) := by
      rw [map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h1 ha) hb
  obtain ⟨h, hh⟩ := exists_canon X hdiff hoff
  have hg := canon_graded 𝒜 X h hdiff hX hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  have hXp' : X.map (p : R →+* R') = (r' x).mat := hXp
  rw [hXp'] at hh'
  exact ⟨h, hh.hat, hg.1, hh'.hat, (cond_iff_canon η Ψ I r' x _ hr hx hΨ hh').1.1 hc⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.PtSign
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem wtPart_decomp {O σ : Type} [CommRing O] (wt : σ → ℤ) (j : ℤ) (s : Finset σ) :
    ∀ f ∈ wtPart O wt j, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ O, (∀ i, g i ∈ wtPart O wt (j - wt i)) ∧
        f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  intro f hf hs
  let P : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : ∃ k ∈ s, n k ≠ 0, h.choose = i
  let g : σ → MvPowerSeries σ O := fun i m =>
    if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 :=
    fun _ _ => rfl
  refine ⟨g, fun i m hm => ?_, ?_⟩
  · rw [hg]
    split_ifs
    · apply hf
      rw [map_add (f := _)]
      intro h
      apply hm
      have : (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
        rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp
      omega
    · rfl
  · have key : ∀ n i, MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
        if P n i then MvPowerSeries.coeff n f else 0 := by
      intro n i
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      by_cases hle : Finsupp.single i 1 ≤ n
      · rw [if_pos hle, one_mul, hg, tsub_add_cancel_of_le hle]
      · have hP : ¬ P n i := by
          rintro ⟨h, hc⟩
          apply hle
          rw [Finsupp.single_le_iff, ← hc]
          exact Nat.one_le_iff_ne_zero.mpr h.choose_spec.2
        rw [if_neg hle, if_neg hP]
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [key]
    by_cases h : ∃ k ∈ s, n k ≠ 0
    · have hP : ∀ i, P n i ↔ h.choose = i := fun i => ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩
      simp_rw [hP]
      rw [Finset.sum_ite_eq, if_pos h.choose_spec.1]
    · have hP : ∀ i, ¬ P n i := fun i ⟨h', _⟩ => h h'
      simp only [hP, if_false, Finset.sum_const_zero]
      push_neg at h
      exact hs n h

private theorem vanish_of_entries {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : F.Adapted u W) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (M : AddSubmonoid ℤ)
    (h : ∀ g, F.η g = 1 → ∀ a b, wt a b ∉ M → ptMat u ξ g a b = 0) (j : ℤ) (hj : j ∉ M) (x : R)
    (hx : x ∈ wpart (O := O) u j) : ξ ⟨x, mem_Sring u hx⟩ = 0 := by
  classical
  haveI := W.fin
  have hmemz : ∀ i, W.z i ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := W.wt i) (by rw [← hW.part]; exact W.z_mem i)
  have hzero : ∀ i, W.wt i ∉ M → ξ ⟨W.z i, hmemz i⟩ = 0 := by
    intro i hi
    obtain ⟨g, a, b, hη, hw, hz⟩ := hW.var i
    have hab : a ≠ b := by
      rintro rfl
      apply hi
      rw [hw]
      simp [wt]
    have hrz : ((F.rz R) g).mat a b = 0 := by
      show algebraMap O R ((((tor O) (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
      rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
    have h1 : ξ ⟨W.z i, hmemz i⟩ = ptMat u ξ g a b := by
      show ξ ⟨W.z i, hmemz i⟩ = ξ ⟨(u g).mat a b, _⟩
      congr 1
      exact Subtype.ext (show W.z i = (u g).mat a b by rw [hz, hrz, sub_zero])
    rw [h1]
    exact h g hη a b (hw ▸ hi)
  rw [← hW.part] at hx
  obtain ⟨f, hf, hfx⟩ := hx
  subst hfx
  let s := Finset.univ.filter (fun i => W.wt i ∉ M)
  have hs : ∀ n : W.σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0 := by
    intro n hn
    apply hf
    intro hw
    apply hj
    rw [← hw, Finsupp.weight_apply]
    refine AddSubmonoid.sum_mem M fun c hc => ?_
    by_cases hcM : W.wt c ∈ M
    · exact nsmul_mem hcM _
    · exact absurd (hn c (by simp [s, hcM])) (Finsupp.mem_support_iff.mp hc)
  obtain ⟨g, hg, hfg⟩ := wtPart_decomp W.wt j s f hf hs
  have hmemg : ∀ i, W.π (g i) ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := j - W.wt i) (by rw [← hW.part]; exact ⟨g i, hg i, rfl⟩)
  have hsum : (⟨W.π.toLinearMap f, mem_Sring u (by rw [← hW.part]; exact ⟨f, hf, rfl⟩)⟩ : Sring (O := O) u) =
      ∑ i ∈ s, (⟨W.z i, hmemz i⟩ : Sring (O := O) u) * ⟨W.π (g i), hmemg i⟩ := by
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hfg, map_sum, WPres.z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [map_mul, hzero i (Finset.mem_filter.mp hi).2, zero_mul]

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_sign :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K)
    (r : Γ →* GG (m := 3) (R := K)), IsPtHom u ξ r →
      (Upper F.η r ↔ ∀ j < 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) ∧
      (Lower F.η r ↔ ∀ j > 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu K _ _ ξ r hr
  obtain ⟨W, hW, _⟩ := exists_adapted F hF g₁ hg₁ u hu
  have hent : ∀ g a b, (r g).mat a b = ptMat u ξ g a b := fun g a b => by rw [(hr g).2]
  let Mp : AddSubmonoid ℤ :=
    { carrier := {n | 0 ≤ n}
      add_mem' := by
        intro a b ha hb
        show 0 ≤ a + b
        exact add_nonneg ha hb
      zero_mem' := le_refl (0 : ℤ) }
  let Mn : AddSubmonoid ℤ :=
    { carrier := {n | n ≤ 0}
      add_mem' := by
        intro a b ha hb
        show a + b ≤ 0
        exact add_nonpos ha hb
      zero_mem' := le_refl (0 : ℤ) }
  have hMp : ∀ n : ℤ, n ∈ Mp ↔ 0 ≤ n := fun _ => Iff.rfl
  have hMn : ∀ n : ℤ, n ∈ Mn ↔ n ≤ 0 := fun _ => Iff.rfl
  refine ⟨⟨fun hU j hj x hx => ?_, fun hv g hg a b hab => ?_⟩, ⟨fun hL j hj x hx => ?_, fun hv g hg a b hab => ?_⟩⟩
  · refine vanish_of_entries F u W hW ξ Mp (fun g hg a b hab => ?_) j (by rw [hMp]; omega) x hx
    rw [← hent]
    exact hU g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMp] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
  · refine vanish_of_entries F u W hW ξ Mn (fun g hg a b hab => ?_) j (by rw [hMn]; omega) x hx
    rw [← hent]
    exact hL g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMn] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
end

