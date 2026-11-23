module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Lemmata.GeneralBFactRightBisAlt.Imports

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable (D : D7)

abbrev aaF (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem entry_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) (hcb : c < b) : ∀ x ∈ aaF D b, x * fmat D G n c b ∈ aaF D c := by
  have hc : c.val < D.R.rS := by have := b.isLt; omega
  have hf : fmat D G n c b = G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, hc⟩ := by
    simp only [fmat, dif_pos hc]
    rw [if_neg (ne_of_lt hcb), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  have haF : aaF D c = aaI D ⟨c.val, hc⟩ := rfl
  rw [haF]
  intro x hx
  by_cases hb : b.val < D.R.rS
  · have hfi : frame G b = G.fl.e ⟨b.val, hb⟩ := by
      have h0 := frame_castSucc G ⟨b.val, hb⟩
      rwa [show (⟨b.val, hb⟩ : Fin D.R.rS).castSucc = b from Fin.ext rfl] at h0
    rw [hfi]
    have hxe : x • G.fl.e ⟨b.val, hb⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨b.val, hb⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨b.val, hb⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hcx := (coefX_of_mem_XS D G.fl hn1).2 ⟨c.val, hc⟩
    have hd : n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨b.val, hb⟩) =
        x • (G.fl.e ⟨b.val, hb⟩ + (n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩)) := by
      rw [map_smul]; congr 1; abel
    have hne : (⟨b.val, hb⟩ : Fin D.R.rS) ≠ ⟨c.val, hc⟩ := by
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e, if_neg hne,
      zero_add] at hcx
    exact hcx
  · have hfz : frame G b = G.fl.z := by
      have h0 := frame_last G
      rwa [show Fin.last D.R.rS = b from Fin.ext (by have := b.isLt; simp; omega)] at h0
    rw [hfz]
    have hb0 : aaF D b = 1 := by
      have : (D.R.rS : ℤ) - (b : ℕ) = 0 := by have := b.isLt; push_cast; omega
      simp only [aaF, this, neg_zero, zpow_zero]
    rw [hb0] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hcx := (coefX_of_mem_XS D G.fl hv).2 ⟨c.val, hc⟩
    rw [← Algebra.smul_def]
    exact fi_smul _ o hcx

end Glob

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAT
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThCorr (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t₁ t₂ : Term V M r)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'),
    H.IsGeneric t₁ → H.IsGeneric t₂ → H.Respects t₁ t₂ φ φ' →
    ∀ (w₁ : V) (hw₁ : w₁ ∈ H.W0 t₁.f t₁.f') (w₂ : V) (hw₂ : w₂ ∈ H.W0 t₂.f t₂.f'),
      φ (H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩) = H.mkW t₂.f ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ →
      φ' (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩) = H.mkW t₂.f' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ →
      (w₁ ∈ t₁.abelian₂ ↔ w₂ ∈ t₂.abelian₂)

theorem mem_iff_of_image_eq {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) {S : Set A} {T : Set B} (h : φ '' S = T) {a : A} {b : B} (hab : φ a = b) :
    a ∈ S ↔ b ∈ T := by
  subst hab
  subst h
  exact φ.injective.mem_set_image.symm

theorem thCorr_holds (M : Model F E) (r : ℕ) : ThCorr M r := by
  intro V _ _ H t₁ t₂ φ φ' hg₁ hg₂ hR w₁ hw₁ w₂ hw₂ he he'
  obtain ⟨hL, -, hL', -, hι⟩ := hR
  have e1 := mem_iff_of_image_eq φ hL he
  have e2 := mem_iff_of_image_eq φ' hL' he'
  cases hs : M.split with
  | none =>
    exact (lemma0L_holds M r hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 e2).trans (lemma0L_holds M r hs V H t₂ hg₂ w₂ hw₂).symm)
  | some g =>
    have hinj : Function.Injective (Prod.map φ' φ) := φ'.injective.prodMap φ.injective
    have e3 := hinj.mem_set_image (s := H.iotaGraph g t₁)
      (a := (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩, H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩))
    rw [hι g hs, Prod.map_apply, he, he'] at e3
    exact (lemma0G_holds M r g hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 (and_congr e2 e3.symm)).trans (lemma0G_holds M r g hs V H t₂ hg₂ w₂ hw₂).symm)

end T

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfGrp
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabIntGrp

section Tri

variable {K : Type*} [CommRing K] {n : ℕ}

def LoIn (S : Subring K) (l : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ S

theorem loIn_lower {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (h : LoIn S l) : l.IsLowerTriangular := by
  intro i j hij
  exact h.2.1 i j hij

theorem mul_diag_of_lower {l l' : Matrix (Fin n) (Fin n) K} (hl : ∀ a b, a < b → l a b = 0)
    (hl' : ∀ a b, a < b → l' a b = 0) (a : Fin n) : (l * l') a a = l a a * l' a a := by
  first | exact Bl.general_b_fact_right_bis_other.goal1 .. | (apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' a | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› | exact @Bl.general_b_fact_right_bis_other.goal1 K

theorem loIn_one (S : Subring K) : LoIn S (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => ?_⟩
  by_cases h : a = b
  · subst h; rw [Matrix.one_apply_eq]; exact S.one_mem
  · rw [Matrix.one_apply_ne h]; exact S.zero_mem

theorem loIn_mul {S : Subring K} {l l' : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) (hl' : LoIn S l') :
    LoIn S (l * l') := by
  refine ⟨fun a => by rw [mul_diag_of_lower hl.2.1 hl'.2.1, hl.1, hl'.1, one_mul], fun a b hab => ?_,
    fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with h | h
    · rw [hl.2.1 a c h, zero_mul]
    · rw [hl'.2.1 c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact S.sum_mem fun c _ => S.mul_mem (hl.2.2 a c) (hl'.2.2 c b)

theorem det_loIn {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : l.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular l (loIn_lower hl)]
  exact Finset.prod_eq_one fun a _ => hl.1 a

theorem loIn_inv {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : LoIn S l⁻¹ := by
  have hd : IsUnit l.det := by rw [det_loIn hl]; exact isUnit_one
  have hinv : l⁻¹ = l.adjugate := by rw [Matrix.inv_def, det_loIn hl, Ring.inverse_one, one_smul]
  letI : Invertible l := Matrix.invertibleOfIsUnitDet l hd
  have hlow : l⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular (loIn_lower hl)
  have hlow' : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b h => hlow h
  refine ⟨fun a => ?_, hlow', fun a b => ?_⟩
  · have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul l hd) a) a
    rw [mul_diag_of_lower hlow' hl.2.1, hl.1, mul_one, Matrix.one_apply_eq] at h1
    exact h1
  · let lS : Matrix (Fin n) (Fin n) S := fun i j => ⟨l i j, hl.2.2 i j⟩
    have hmap : l = S.subtype.mapMatrix lS := by ext i j; rfl
    rw [hinv, hmap, ← RingHom.map_adjugate]
    exact (lS.adjugate a b).2

theorem upIn_iff (S : Subring K) (ρ : Matrix (Fin n) (Fin n) K) :
    ((∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ S) ↔ LoIn S ρ.transpose := by
  unfold LoIn
  simp only [Matrix.transpose_apply]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩⟩

end Tri

section Loc

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

theorem intUp_iff (ρ : Matrix (Fin n) (Fin n) E) : Formalism.MainNotions.S.TieN.IntUp Mp ρ ↔ LoIn Mp.R ρ.transpose :=
  upIn_iff Mp.R ρ

theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) := loIn_one _

theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) := by
  rw [intUp_iff, Matrix.transpose_one]; exact loIn_one _

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := loIn_mul h h'

theorem intUp_mul {ρ ρ' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp ρ') : Formalism.MainNotions.S.TieN.IntUp Mp (ρ * ρ') := by
  rw [intUp_iff] at *; rw [Matrix.transpose_mul]; exact loIn_mul h' h

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ := loIn_inv h

theorem intUp_inv {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) :
    Formalism.MainNotions.S.TieN.IntUp Mp ρ⁻¹ := by
  rw [intUp_iff] at *; rw [Matrix.transpose_nonsing_inv]; exact loIn_inv h

theorem intLow_det {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) : IsUnit l.det := by
  rw [det_loIn h]; exact isUnit_one

theorem intUp_det {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) : IsUnit ρ.det := by
  rw [intUp_iff] at h; rw [← Matrix.det_transpose, det_loIn h]; exact isUnit_one

end Loc

section Field

variable {E : Type*} [Field E] {n : ℕ}

theorem isLoUni_iff (a : Matrix (Fin n) (Fin n) E) : IsLoUni a ↔ LoIn (⊤ : Subring E) a := by
  unfold IsLoUni LoIn
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

theorem isUpUni_iff (b : Matrix (Fin n) (Fin n) E) : IsUpUni b ↔ LoIn (⊤ : Subring E) b.transpose := by
  rw [← upIn_iff]
  unfold IsUpUni
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

end Field

theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  funext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word) (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
  (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_set : (1 : GLR D) ∈ stabIntSet D u u' δ M w := by
  refine ⟨(isLoUni_iff _).2 (by simpa using loIn_one _), 1, (isUpUni_iff _).2 (by simpa using loIn_one _),
    by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z => ?_⟩⟩
  simp [zhatOM_zhatOM]

theorem mul_mem_set {a a' : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) (ha' : a' ∈ stabIntSet D u u' δ M w) :
    a * a' ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  obtain ⟨hla', b', hb', hab', hp'⟩ := ha'
  refine ⟨?_, b' * b, ?_, ?_, fun p => ?_⟩
  · rw [Units.val_mul, isLoUni_iff]; exact loIn_mul ((isLoUni_iff _).1 hla) ((isLoUni_iff _).1 hla')
  · rw [isUpUni_iff, Matrix.transpose_mul]; exact loIn_mul ((isUpUni_iff _).1 hb) ((isUpUni_iff _).1 hb')
  · rw [Units.val_mul]
    calc (a : MatR D) * a' * ptMat w * (b' * b) = (a : MatR D) * ((a' : MatR D) * ptMat w * b') * b := by
          simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hab', hab]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    obtain ⟨l', ρ', hl', hρ', hm'⟩ := hp' p
    refine ⟨l * l', ρ' * ρ, intLow_mul _ hl hl', intUp_mul _ hρ' hρ, fun Z => ?_⟩
    have e : ((a * a' : GLR D) : MatR D) * ZhatOM Z * (b' * b) =
        (a : MatR D) * ZhatOM (ZhatOM ((a' : MatR D) * ZhatOM Z * b')) * b := by
      rw [zhatOM_zhatOM, Units.val_mul]; simp only [Matrix.mul_assoc]
    rw [e, hm, hm']
    simp only [Matrix.mul_assoc]

theorem inv_mem_set {a : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) : a⁻¹ ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  have hbT := (isUpUni_iff _).1 hb
  have hbd : IsUnit b.det := by rw [← Matrix.det_transpose, det_loIn hbT]; exact isUnit_one
  have hai : ((a⁻¹ : GLR D) : MatR D) = (a : MatR D)⁻¹ := Matrix.coe_units_inv a
  have had : IsUnit (a : MatR D).det := by rw [det_loIn ((isLoUni_iff _).1 hla)]; exact isUnit_one
  refine ⟨?_, b⁻¹, ?_, ?_, fun p => ?_⟩
  · rw [hai, isLoUni_iff]; exact loIn_inv ((isLoUni_iff _).1 hla)
  · rw [isUpUni_iff, Matrix.transpose_nonsing_inv]; exact loIn_inv hbT
  · rw [hai]
    calc (a : MatR D)⁻¹ * ptMat w * b⁻¹ = (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ := by rw [hab]
      _ = ptMat w := by
        rw [show (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ =
            ((a : MatR D)⁻¹ * (a : MatR D)) * ptMat w * (b * b⁻¹) by simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ had, Matrix.mul_nonsing_inv _ hbd, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    refine ⟨l⁻¹, ρ⁻¹, intLow_inv _ hl, intUp_inv _ hρ, fun Z => ?_⟩
    set Z' := ZhatOM (((a⁻¹ : GLR D) : MatR D) * ZhatOM Z * b⁻¹) with hZ'
    have e : (a : MatR D) * ZhatOM Z' * b = ZhatOM Z := by
      rw [hZ', zhatOM_zhatOM, hai, show (a : MatR D) * ((a : MatR D)⁻¹ * ZhatOM Z * b⁻¹) * b =
          ((a : MatR D) * (a : MatR D)⁻¹) * ZhatOM Z * (b⁻¹ * b) by simp only [Matrix.mul_assoc],
        Matrix.mul_nonsing_inv _ had, Matrix.nonsing_inv_mul _ hbd, Matrix.one_mul, Matrix.mul_one]
    have h1 := hm Z'
    rw [e, zhatOM_zhatOM] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (intLow_det _ hl), Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (intUp_det _ hρ)]

def stabIntGrp : Subgroup (GLR D) where
  carrier := stabIntSet D u u' δ M w
  one_mem' := one_mem_set D u u' δ M w
  mul_mem' := mul_mem_set D u u' δ M w
  inv_mem' := inv_mem_set D u u' δ M w

theorem stabInt_eq : stabInt D u u' δ M w = stabIntGrp D u u' δ M w := by
  unfold stabInt
  exact Subgroup.closure_eq (stabIntGrp D u u' δ M w)

theorem mem_stabInt_iff (a : GLR D) : a ∈ stabInt D u u' δ M w ↔ a ∈ stabIntSet D u u' δ M w := by
  rw [stabInt_eq]; rfl

end Formalism.L2.SG.Pf.StabIntGrp
end
end

