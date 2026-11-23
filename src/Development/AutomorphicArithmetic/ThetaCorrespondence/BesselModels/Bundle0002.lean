module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HWSpan
public import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.KShift

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IrreducibleUnitaryRepIsoHarishChandraType
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.HWSpanType

theorem exists_hcType_of_irred : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  intro k Wp _ _ _ _ ρ hρ hirr
  obtain ⟨E, hgl, hun, hE⟩ := Derived.exists_derived_action k Wp ρ hρ
  have hQ : CompanionTheory.D.DSIC.KStab (PI.UpqRep.allPos k) E (⊤ : Submodule ℂ Wp) := fun _ _ _ _ _ => trivial
  obtain ⟨μ, x, -, hx0, hx⟩ := UpperTheory.Lit.Bur.KShift.exists_highest hgl (UpperTheory.Lit.Bur.KShift.kUnit_of hun) hQ top_ne_bot
  have hlow : PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k) = μ := by
    rw [GlobalTheory.KTypeCompare.lowK_allPos]
    simp
  have hΛ : Formalism.REAL.KHighest (PI.UpqRep.allPos k) E
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) (μ + GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.rhoU k)) x := by
    rw [hlow]; exact hx
  have htype := exists_type_of_highest hρ E hgl hun hE _ x hx0 hΛ
  set S := Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x with hS
  have hst := Wt.stable_of_derived hρ E hE S (Formalism.REAL.isCompactInvariant_compactSpan x)
  have hxS : x ∈ S := Formalism.REAL.mem_compactSpan x
  have htop : S = ⊤ := (hirr S hst).resolve_left fun h => hx0 (by
    rw [h] at hxS; exact (Submodule.mem_bot ℂ).1 hxS)
  refine ⟨_, S, inferInstance, inferInstance, compress ρ S, (LinearEquiv.ofTop S htop).symm, htype, ?_⟩
  intro h hh w
  apply Subtype.ext
  rw [coe_compress (hst h hh _ (Subtype.property _))]
  simp [LinearEquiv.ofTop_symm_apply]

end UpperTheory.Lit.Bur.HWSpanType

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType : ∀ {k : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [Nontrivial Wp] {ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)} (hρ : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ) (hirr : ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤), ∃ (u : Fin k → ℝ) (Wq : Type) (_ : NormedAddCommGroup Wq) (_ : InnerProductSpace ℂ Wq) (ρ' : Matrix (Fin k) (Fin k) ℂ → (Wq →L[ℂ] Wq)) (T : Wp ≃ₗ[ℂ] Wq), PI.UpqRep.IsHCTypeU k u ρ' ∧ ∀ h ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ w, T (ρ h w) = ρ' h (T w) := by
  first | exact @UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | exact UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred | (intros; apply UpperTheory.Lit.Bur.HWSpanType.exists_hcType_of_irred <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsFrameExistsIsotropicDualColumns
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.DualCols


open scoped ComplexOrder in
theorem exists_right_inv {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hJ : IsUnit J) (he : LinearIndependent ℂ eᵀ) : ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 := by
  have hr : eᵀ.rank = r := by simpa using LinearIndependent.rank_matrix (M := eᵀ) he
  have hr2 : (eᴴ * J).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det J).1 hJ),
      Matrix.rank_conjTranspose, ← Matrix.rank_transpose, hr]
  have hs : Function.Surjective (eᴴ * J).mulVec := by
    have h : LinearMap.range (eᴴ * J).mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank] using hr2)
    exact LinearMap.range_eq_top.1 h
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs

theorem adj {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) {α β : Type} [Fintype α] [Fintype β]
    (X : Matrix (Fin n) α ℂ) (Y : Matrix (Fin n) β ℂ) : (Xᴴ * J * Y)ᴴ = Yᴴ * J * X := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]

theorem core {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e f' : Matrix (Fin n) (Fin r) ℂ} {Z : Matrix (Fin n) Unit ℂ} {c : ℂ}
    (hJ : Jᴴ = J) (hd : IsUnit J₀.det) (hc : c ≠ 0) (hFF : Fᴴ * J * F = J₀) (hFe : Fᴴ * J * e = 0)
    (hFZ : Fᴴ * J * Z = 0) (hee : eᴴ * J * e = 0) (heZ : eᴴ * J * Z = 0) (hZZ : Zᴴ * J * Z = c • 1)
    (hf' : eᴴ * J * f' = 1) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ Zᴴ * J * f = 0 := by
  have heF : eᴴ * J * F = 0 := by rw [← adj hJ F e, hFe, conjTranspose_zero]
  have hZF : Zᴴ * J * F = 0 := by rw [← adj hJ F Z, hFZ, conjTranspose_zero]
  have hZe : Zᴴ * J * e = 0 := by rw [← adj hJ e Z, heZ, conjTranspose_zero]
  obtain ⟨P, hP⟩ : ∃ P, J₀ * P = Fᴴ * J * f' :=
    ⟨J₀⁻¹ * (Fᴴ * J * f'), by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Zᴴ * J * Z * Q = Zᴴ * J * f' :=
    ⟨c⁻¹ • (Zᴴ * J * f'), by rw [hZZ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨f₂, h₂⟩ : ∃ f₂, f₂ = f' - F * P - Z * Q := ⟨_, rfl⟩
  have hF₂ : Fᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hFF, hFZ, hP,
      Matrix.zero_mul, sub_self, sub_zero]
  have hZ₂ : Zᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hZF, hQ,
      Matrix.zero_mul, sub_zero, sub_self]
  have he₂ : eᴴ * J * f₂ = 1 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, heF, heZ, hf',
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have he₂' : f₂ᴴ * J * e = 1 := by rw [← adj hJ e f₂, he₂, conjTranspose_one]
  obtain ⟨H, hH, hHH⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, Hᴴ = H ∧ H + H = f₂ᴴ * J * f₂ := by
    refine ⟨(1 / 2 : ℝ) • (f₂ᴴ * J * f₂), ?_, ?_⟩
    · rw [conjTranspose_smul, adj hJ f₂ f₂]; simp
    · rw [← add_smul]; norm_num
  have hfH : (f₂ - e * H)ᴴ = f₂ᴴ - H * eᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, hH]
  refine ⟨f₂ - e * H, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hee, he₂, Matrix.zero_mul, sub_zero]
  · have h1 : (f₂ᴴ - H * eᴴ) * J * f₂ = f₂ᴴ * J * f₂ - H := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, he₂,
        Matrix.mul_one]
    have h2 : (f₂ᴴ - H * eᴴ) * J * e = 1 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, he₂', Matrix.mul_assoc H, Matrix.mul_assoc H, hee,
        Matrix.mul_zero, sub_zero]
    rw [hfH, Matrix.mul_sub, ← Matrix.mul_assoc _ e, h1, h2, Matrix.one_mul, ← hHH]
    abel
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hFe, hF₂, Matrix.zero_mul, sub_zero]
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hZe, hZ₂, Matrix.zero_mul, sub_zero]

theorem exists_dual_cols {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  obtain ⟨f', hf'⟩ := exists_right_inv hf.unit hf.e_indep
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) Unit ℂ, Z = Matrix.of fun i _ => z i := ⟨_, rfl⟩
  have hcol : ∀ {a : Type} (M : Matrix a (Fin n) ℂ) (i : a) (u : Unit), (M * Z) i u = (M *ᵥ z) i := by
    intro a M i u
    subst hZ
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hFZ : Fᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpF]
    rfl
  have heZ : eᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpE]
    rfl
  have hZZ : Zᴴ * J * Z = (Formalism.QuantumDeterminants.herm J z z) • (1 : Matrix Unit Unit ℂ) := by
    ext u v
    subst hZ
    simp [Formalism.QuantumDeterminants.herm, Matrix.mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨f, h1, h2, h3, h4⟩ := core hf.herm ((Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀) hf.z_ne hf.gram
    hf.e_perp hFZ hf.e_iso heZ hZZ hf'
  refine ⟨f, h1, h2, h3, ?_⟩
  have h5 : fᴴ * J * Z = 0 := by rw [← adj hf.herm Z f, h4, conjTranspose_zero]
  funext i
  rw [← hcol _ i (), h5]
  rfl

end UpperTheory.Lit.Bur.DualCols

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns : ∀ {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z), ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  first | exact @UpperTheory.Lit.Bur.DualCols.exists_dual_cols | exact UpperTheory.Lit.Bur.DualCols.exists_dual_cols | (intros; apply UpperTheory.Lit.Bur.DualCols.exists_dual_cols <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsometryConjMapsUnipotentRadical
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.UnipRadConj

theorem conj_mem_unipRad : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e)
    {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  intro n r J G Q Qi e e' h1 h2 hg he u hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hu1' : uᴴ * G * u = G := hu1
  have hw1 : Q * u * Qi - 1 = Q * (u - 1) * Qi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hcol : ∀ i : Fin r, (fun k => e k i) = Q *ᵥ fun k => e' k i := by
    intro i
    rw [← he]
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · show (Q * u * Qi)ᴴ * J * (Q * u * Qi) = J
    calc (Q * u * Qi)ᴴ * J * (Q * u * Qi) = Qiᴴ * (uᴴ * (Qᴴ * J * Q) * u) * Qi := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Qiᴴ * G * Qi := by rw [hg, hu1']
      _ = (Q * Qi)ᴴ * J * (Q * Qi) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [h1]; simp
  · intro i
    obtain ⟨a, ha0, ha⟩ := hu2 i
    refine ⟨a, ha0, ?_⟩
    have hq : Q * (u - 1) * Qi * Q = Q * (u - 1) := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [hw1, hcol i, Matrix.mulVec_mulVec, hq, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]
  · intro x hx
    have hy : (e'ᴴ * G) *ᵥ (Qi *ᵥ x) = 0 := by
      have hm : e'ᴴ * (Qᴴ * J * Q) * Qi = eᴴ * J := by
        rw [← he, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rw [h1, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, ← hg, hm]
      exact hx
    obtain ⟨a, ha⟩ := hu3 _ hy
    refine ⟨a, ?_⟩
    rw [hw1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]

end UpperTheory.Lit.Bur.UnipRadConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  first | exact @UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | exact UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | (intros; apply UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.MemBesselUnipotentRadicalOfMemCoordGroup
section
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselRadical

theorem mem_unipRad_of_mem_Nset {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hu : u ∈ Formalism.QuantumDeterminants.Nset k r) : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  obtain ⟨hU, hcol, hmid⟩ := hu
  have hspan : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) →
      y = colE k r *ᵥ fun b => y (PI.UpqRep.eI k r b) := by
    intro y hy
    funext i
    simp only [Matrix.mulVec, dotProduct, colE, ite_mul, one_mul, zero_mul]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have h : i = PI.UpqRep.eI k r ⟨i, hi⟩ := Fin.ext rfl
        rw [if_pos h, ← h]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (congrArg Fin.val h).symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hy i (not_lt.mp hi)]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact b.isLt
  have key : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) (j : Fin (2 * r + k + 1)), (b : ℕ) + j = 2 * r + k →
      (((colE k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) *ᵥ x) b = x j := by
    intro x b j hbj
    rw [← Matrix.mulVec_mulVec]
    have hc : ∀ w : Fin (2 * r + k + 1) → ℂ, ((colE k r)ᴴ *ᵥ w) b = w (PI.UpqRep.eI k r b) := by
      intro w
      simp [Matrix.mulVec, dotProduct, colE, Matrix.conjTranspose_apply]
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    have hb := b.isLt
    rw [Finset.sum_eq_single j]
    · have h1 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) j = 1 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hbj, hb]
      rw [h1, one_mul]
    · intro m _ hm
      have hne : (b : ℕ) + m ≠ 2 * r + k := fun h => hm (Fin.ext (by omega))
      have h0 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) m = 0 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hne, not_le.mpr hb]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨hU, ?_, ?_⟩
  · intro i
    have hy : ∀ m, ((u - 1) *ᵥ fun m => colE k r m i) m
        = u m (PI.UpqRep.eI k r i) - if m = PI.UpqRep.eI k r i then 1 else 0 := by
      intro m
      simp [Matrix.mulVec, dotProduct, colE, Matrix.sub_apply, Matrix.one_apply, sub_mul]
    refine ⟨fun b => ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r b), ?_, hspan _ ?_⟩
    · intro j hij
      show ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r j) = 0
      rw [hy]
      exact sub_eq_zero.mpr (hcol i _ hij)
    · intro m hm
      rw [hy]
      exact sub_eq_zero.mpr (hcol i m (le_trans (Nat.le_of_lt i.isLt) hm))
  · intro x hx
    have hxz : ∀ j : Fin (2 * r + k + 1), r + k < (j : ℕ) → x j = 0 := by
      intro j hj
      have hjN := j.isLt
      have hb : 2 * r + k - (j : ℕ) < r := by omega
      have h := key x ⟨2 * r + k - j, hb⟩ j (by show 2 * r + k - (j : ℕ) + j = 2 * r + k; omega)
      rw [← h, hx]
      rfl
    refine ⟨fun b => ((u - 1) *ᵥ x) (PI.UpqRep.eI k r b), hspan _ ?_⟩
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : (j : ℕ) ≤ r + k
    · have h0 : (u - 1) i j = 0 := by
        rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
        by_cases hjr : (j : ℕ) < r
        · exact hcol ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)
        · exact hmid i j (not_lt.mp hjr) hj hi
      rw [h0, zero_mul]
    · rw [hxz j (not_le.mp hj), mul_zero]

end UpperTheory.Lit.Bur.BesselRadical

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup : ∀ {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.Nset k r), u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  first | exact @UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | exact UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | (intros; apply UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecConjugateUnitaryGroupIff
section
noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
open scoped ContDiff

namespace UpperTheory.Lit.Bur.SmoothConj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_list_prod {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    Q * l.prod * Qi = (l.map fun g => Q * g * Qi).prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc Q * (a * l.prod) * Qi = Q * a * 1 * l.prod * Qi := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * a * Qi * (Q * l.prod * Qi) := by
          rw [← h2]; simp only [Matrix.mul_assoc]

theorem exp_conj_of_inverse {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Qi)) = Q * NormedSpace.exp (t • X) * Qi := by
  have hi : Qi = Q⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  subst hi
  rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_lieG_of_gram {J G Q Qi X : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hX : X ∈ lieG G) : Q * X * Qi ∈ lieG J := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Q * X * Qi)ᴴ * J + J * (Q * X * Qi) = 0
  calc (Q * X * Qi)ᴴ * J + J * (Q * X * Qi)
      = Qiᴴ * Xᴴ * Qᴴ * J * 1 + 1 * J * Q * X * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = Qiᴴ * Xᴴ * Qᴴ * J * (Q * Qi) + (Qiᴴ * Qᴴ) * J * Q * X * Qi := by rw [h1, hc]
    _ = Qiᴴ * (Xᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * X) * Qi := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hg, hX']; simp

theorem conj_inv_mem_lieG_of_gram {J G Q Qi Y : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hY : Y ∈ lieG J) : Qi * Y * Q ∈ lieG G := by
  have hY' : Yᴴ * J + J * Y = 0 := hY
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Qi * Y * Q)ᴴ * G + G * (Qi * Y * Q) = 0
  subst hg
  calc (Qi * Y * Q)ᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * (Qi * Y * Q)
      = Qᴴ * Yᴴ * (Qiᴴ * Qᴴ) * J * Q + Qᴴ * J * (Q * Qi) * Y * Q := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * (Yᴴ * J + J * Y) * Q := by
        rw [h1, hc]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = 0 := by rw [hY']; simp

theorem smoothVec_conj_of_subset {L L' : Set (Matrix (Fin n) (Fin n) ℂ)}
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {Q Qi : Matrix (Fin n) (Fin n) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hL : ∀ X ∈ L', Q * X * Qi ∈ L) {v : H}
    (hv : SmoothVec L σ v) : SmoothVec L' (fun g => σ (Q * g * Qi)) v := by
  intro k Xs hX
  have h := hv k (fun i => Q * Xs i * Qi) fun i => hL _ (hX i)
  have he : ∀ t : Fin k → ℝ, Q * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Qi =
      (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Qi))).prod := by
    intro t
    rw [conj_list_prod h1 h2, List.map_ofFn]
    congr 1
    congr 1
    funext i
    exact (exp_conj_of_inverse h1 h2 (Xs i) (t i)).symm
  simpa only [he] using h

theorem smoothVec_conj_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * J * Q = G) (v : H) :
    SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  constructor
  · intro h
    have h' := smoothVec_conj_of_subset (L := lieG G) (L' := lieG J)
      (fun g => σ (Q * g * Qi)) h2 h1 (fun Y hY => conj_inv_mem_lieG_of_gram h1 hg hY) h
    have he : (fun g => σ (Q * (Qi * g * Q) * Qi)) = σ := by
      funext g
      have : Q * (Qi * g * Q) * Qi = g := by
        calc Q * (Qi * g * Q) * Qi = (Q * Qi) * g * (Q * Qi) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [h1]; simp
      rw [this]
    rwa [he] at h'
  · exact smoothVec_conj_of_subset σ h1 h2 fun X hX => conj_mem_lieG_of_gram h1 hg hX

end UpperTheory.Lit.Bur.SmoothConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (v : H), SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  first | exact @UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | exact UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | (intros; apply UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecStableUnderUnitaryGroup
section
noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SmoothTranslate

theorem conj_mem_lieG {n : ℕ} {J g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (hg : g ∈ Formalism.QuantumDeterminants.UH J)
    (hX : X ∈ lieG J) : g⁻¹ * X * g ∈ lieG J := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hAB : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hd
  have hBA : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hBA' : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  have h : gᴴ * J * g = J := hg
  have hX' : Xᴴ * J + J * X = 0 := hX
  show (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g)
      = (g⁻¹ * X * g)ᴴ * (gᴴ * J * g) + (gᴴ * J * g) * (g⁻¹ * X * g) := by rw [h]
    _ = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * gᴴ) * J + J * (g * g⁻¹) * X) * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

theorem smoothVec_translate : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H}
    (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  intro n H _ _ J hJ σ hσ g hg v hv k Xs hXs
  have hu : IsUnit g := isUnit_of_mem_UH hJ hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieG J := fun i => conj_mem_lieG hu hg (hXs i)
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((σ g).restrictScalars ℝ).contDiff.comp (hv k _ hY)
  convert h1 using 2 with t
  show σ _ (σ g v) = σ g (σ _ v)
  have hP := expProd_mem_UH hJ hXs t
  have hQ := expProd_mem_UH hJ hY t
  have e1 := hσ.1.2 _ hP _ hg
  have e2 := hσ.1.2 _ hg _ hQ
  have e3 : g * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← mul_prod_conj hu, List.map_ofFn]
    simp only [hc, Function.comp_def]
  have e4 := e1.symm.trans ((congrArg σ e3).symm.trans e2)
  exact congrArg (fun T : H →L[ℂ] H => T v) e4

end UpperTheory.Lit.Bur.SmoothTranslate

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H} (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  first | exact @UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | exact UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | (intros; apply UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate <;> assumption)
end
end

