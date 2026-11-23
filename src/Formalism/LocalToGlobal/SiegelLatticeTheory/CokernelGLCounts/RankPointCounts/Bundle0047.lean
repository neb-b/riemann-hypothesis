module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsLoOfIntLow
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Free

def Free {n : ℕ} (σ : Fin n → Fin n) (i j : Fin n) : Prop := j < i ∧ σ i < σ j

theorem off_free {K : Type*} [CommRing K] {n : ℕ} {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpat : ∀ i j, σ j < σ i → T i j = 0) {i j : Fin n}
    (h : ¬ Free σ i j) : T i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hT.2 i j hij, Matrix.one_apply_ne hij.ne]
  · rw [hT.1 i, Matrix.one_apply_eq]
  · have hne : σ i ≠ σ j := fun e => hij.ne' (by rw [← hσ i, e, hσ])
    have : σ j < σ i := by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ⟨hij, h'⟩ h
      · exact h'
    rw [hpat i j this, Matrix.one_apply_ne hij.ne']

theorem ent_free {E K : Type*} [Field E] [CommRing K] (ψ : E →+* K) {n : ℕ} {σ : Fin n → Fin n}
    (hσ : ∀ a, σ (σ a) = a) {X' : Matrix (Fin n) (Fin n) E} (hX' : IsLo X') (hpX : ∀ i j, σ j < σ i → X' i j = 0)
    {T : Matrix (Fin n) (Fin n) K} (hT : IsLo T) (hpT : ∀ i j, σ j < σ i → T i j = 0) {J : AddSubgroup K}
    (h : ∀ i j, Free σ i j → ψ (X' i j) - T i j ∈ J) : EntIn J (X'.map ψ - T) := by
  intro i j
  rw [Matrix.sub_apply, Matrix.map_apply]
  by_cases hf : Free σ i j
  · exact h i j hf
  · rw [off_free hσ hX' hpX hf, off_free hσ hT hpT hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem bnd_mats {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K} (O : Subring Fp)
    (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) (hx : ∀ x : K, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * x ∈ I)
    {n k : ℕ} (Ms : Fin k → Matrix (Fin n) (Fin n) K) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ m i j, algebraMap Fp K s * Ms m i j ∈ I := by
  obtain ⟨s, hs0, hsO, hs⟩ := bnd_fin O hI (fun q : Fin k × Fin n × Fin n => Ms q.1 q.2.1 q.2.2) (fun q => hx _)
  exact ⟨s, hs0, hsO, fun m i j => hs (m, i, j)⟩

theorem int_of_close {K : Type*} [CommRing K] {I : Subring K} {n : ℕ} {a : Matrix (Fin n) (Fin n) K}
    (h : EntIn (lat I 1) (a - 1)) (i j : Fin n) : a i j ∈ I := by
  have e : a i j = (a - 1) i j + (1 : Matrix (Fin n) (Fin n) K) i j := by rw [Matrix.sub_apply]; ring
  rw [e]
  refine I.add_mem (lat_one (h i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact I.one_mem
  · exact I.zero_mem

end Free

section BadL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def GoodAt (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ X' : PairVal.MatR D) : Prop :=
  TieN.IntLow (Zd.M p) (locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) ∧
    TieN.IntUp (Zd.M p) (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀))

def LocTarget (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (L₁ U₁ A₀ B₀ : PairVal.MatR D) : Prop :=
  ∃ (T : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (c : (D.s.atP p).Fp), c ≠ 0 ∧
    ∀ X' : PairVal.MatR D, IsLo X' → (∀ i j, fσ w j < fσ w i → X' i j = 0) →
      (∀ i j, Free (fσ w) i j → ∃ y ∈ (D.s.atP p).O,
        (D.s.atP p).ιE (X' i j) - T i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y) →
      GoodAt Zd p w L₁ U₁ A₀ B₀ X'

theorem isLo_of_intLow {p : PlF D} {l : MatP D p} (h : TieN.IntLow (Zd.M p) l) : IsLo l := ⟨h.1, h.2.1⟩

theorem isUp_of_intUp {p : PlF D} {ρ : MatP D p} (h : TieN.IntUp (Zd.M p) ρ) : IsUp ρ :=
  ⟨h.1, fun a b hab => h.2.1 b a hab⟩

theorem target_L (u u' : D.what₂.Word) (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  have hcv : ∀ a, (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) a *
      (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) a = 1 :=
    fun a => by simp only [← map_mul, cf_cfi, map_one]
  have hσ : ∀ a, fσ w (fσ w a) = a := fσ_fσ w
  have hν : ∀ a : Fin (D.R.rS + 1), pv w.1 a ≠ 0 := fun a => pv_ne' w a
  have hYp : CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p =
      (1 : (D.s.atP p).Ep) • (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * mono (fσ w) (fun a => pv w.1 a) * U₁).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))) -
      (0 : (D.s.atP p).Ep) • Ecorner D.R.rS := by
    rw [one_smul, zero_smul, sub_zero, zzp_sgn_ord Zd u u' p hM Z₁, hZ, ptMat_mono']
  obtain ⟨hli, -, hll'⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨hρi, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  have hkL : IsLo (l⁻¹ * locL Zd p A₀ B₀) := isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p hA₀ hB₀)
  have hkR : IsUp (locR Zd p A₀ B₀ * ρ⁻¹) := isUp_mul (locR_up Zd p hA₀ hB₀) (isUp_of_intUp Zd hρi)
  have hk := key_stab Zd p hl hρ h
  rw [hYp] at hk
  obtain ⟨hTlo, hTpat, -⟩ := comp_target (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk
  obtain ⟨t, ht0, htO, hb⟩ := bnd_mats 𝒪[(D.s.atP p).Fp] (fun s hs => alg_mem_O hs) (fun x => bounded x)
    ![cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁,
      cQ (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) U₁,
      cQ' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) U₁,
      Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i), Matrix.of fun i _ => (D.s.atP p).ιE (pv w.1 i)⁻¹,
      cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁]
  refine ⟨(cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹,
    t * (t * (t * (t * (t * 1)))), by simp [ht0], ?_⟩
  intro X' hX' hpat hfree
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ hZ hX' hpat
  have hab := key_stab Zd p hl hρ ((corr_move Zd u u' p hA₀ hB₀ hgX hgY hst).trans h)
  rw [hYp] at hab
  have ha : IsLo (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) :=
    isLo_mul (isLo_of_intLow Zd hli) (locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀))
  have hb' : IsUp (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) :=
    isUp_mul (locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)) (isUp_of_intUp Zd hρi)
  have haX : l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) = (l⁻¹ * locL Zd p A₀ B₀) *
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
        (L₁ * X' * L₁⁻¹).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))) := by
    rw [locL_L Zd p hM, locL_L Zd p hM, gX, Matrix.map_mul (L := A₀)]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)))
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))), diag_one (hcv'_of hcv),
      Matrix.one_mul]
  have hG : EntIn (lat (D.s.atP p).O (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t * 1))))))
      (X'.map (D.s.atP p).ιE - (cP' (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) L₁ *
        (l⁻¹ * locL Zd p A₀ B₀) * cP (D.s.atP p).ιE (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) L₁)⁻¹) := by
    refine ent_free (D.s.atP p).ιE hσ hX' hpat hTlo hTpat fun i j hf => ?_
    obtain ⟨y, hy, e⟩ := hfree i j hf
    refine ⟨y, hy, ?_⟩
    rw [e]
    simp only [map_mul, map_one]
  have hcl := comp_main (D.s.atP p).ιE hcv hL₁ hU₁ hσ hν isUnit_one hkL hkR hk ha hb' hab haX
    (alg_mem_O htO) (D.s.atP p).O.one_mem
    (fun a => by simpa using hb 4 a a) (fun a => by simpa using hb 5 a a)
    (fun i j => by simpa using hb 0 i j) (fun i j => by simpa using hb 1 i j)
    (fun i j => by simpa using hb 2 i j) (fun i j => by simpa using hb 3 i j)
    (fun i j => by simpa using hb 6 i j) hG
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  refine ⟨?_, ?_⟩
  · have e : locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        l * (l⁻¹ * locL Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀)) := by
      rw [← Matrix.mul_assoc, hll', Matrix.one_mul]
    rw [e]
    refine ZsVolGrp.intLow_mul (Zd.M p) hl ⟨ha.1, ha.2, fun i j => ?_⟩
    rw [hR]
    exact int_of_close hcl.1 i j
  · have e : locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) =
        (locR Zd p (A₀ * gX L₁ X') (gY w U₁ X' * B₀) * ρ⁻¹) * ρ := by
      rw [Matrix.mul_assoc, (ZsVolGrp.intUp_inv (Zd.M p) hρ).2.1, Matrix.mul_one]
    rw [e]
    refine ZsVolGrp.intUp_mul (Zd.M p) ⟨hb'.1, fun a b hab => hb'.2 b a hab, fun i j => ?_⟩ hρ
    rw [hR]
    exact int_of_close hcl.2 i j

end BadL

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def GamG (t : Term V M r) (g : Fin (r + 1) → V) : Set (DDt H t × H.Wb g) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X g)), p = (ddMk H t u, H.mkW g ⟨u, hu⟩)}

theorem mkW_add {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a + b, Submodule.add_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ + H.mkW g ⟨b, hb⟩ := by
  rw [← map_add (f := _)]
  rfl

theorem mkW_sub {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a - b, Submodule.sub_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ - H.mkW g ⟨b, hb⟩ := by
  rw [← map_sub]
  rfl

theorem mkW_congr {g : Fin (r + 1) → V} {a b : V} (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g))
    (h : a = b) : H.mkW g ⟨a, ha⟩ = H.mkW g ⟨b, hb⟩ := by
  subst h
  rfl

theorem spanMM_le_U (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hsup : Submodule.span E (Set.range (Sum.elim t.f t.f')) = H.Xp t.f ⊔ H.Xp t.f' := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    rfl
  rw [hsup]
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)

theorem claimR_side (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f'))
    (hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f'))
    (hsd₁ : H.IsSelfDual t₁.abelian₂) (hsd₂ : H.IsSelfDual Λ₂)
    (hMM₁ : MMo H t₁ ≤ t₁.abelian₂) (hMM₂ : MMo H t₂ ≤ Λ₂)
    (hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂)
    (hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂)
    (g₁ g₂ : Fin (r + 1) → V)
    (hY₂ : H.X g₂ ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
    (hW₁ : H.W0 t₁.f t₁.f' ≤ H.perp (H.X g₁)) (hW₂ : H.W0 t₂.f t₂.f' ≤ H.perp (H.X g₂))
    (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂)
    (hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'), χ (H.mkW g₁ ⟨w, hW₁ w.2⟩) = H.mkW g₂ ⟨ψ w, hW₂ (ψ w).2⟩)
    (hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩) :
    χ '' H.Lset t₁.abelian₂ g₁ = H.Lset Λ₂ g₂ ↔
      (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ = GamG H t₂ g₂ := by

  have hsep₂ : ∀ (a b : V) (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
      (hb : b ∈ H.W0 t₂.f t₂.f') (ha' : a ∈ H.perp (H.X g₂)),
      H.mkW g₂ ⟨a, ha'⟩ = H.mkW g₂ ⟨b, hW₂ hb⟩ → b = 0 := by
    intro a b ha hb ha' hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    have h2 : b = a - (a - b) := by abel
    have h3 : b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
      rw [h2]; exact Submodule.sub_mem _ ha (hY₂ h1)
    exact (Submodule.disjoint_def.1 hU₂.disjoint) b h3 hb
  have hpart : ∀ (t : Term V M r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → MMo H t ≤ Λ →
      ∀ a b : V, a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → b ∈ H.W0 t.f t.f' → a + b ∈ Λ →
        a ∈ MMsharp H t := by
    intro t Λ hsd hMM a b ha hb hab
    refine ⟨span_frames_le_MM H t ha, fun μ hμ => ?_⟩
    have hμU : μ ∈ Submodule.span E (Set.range (H.MMfam t)) := Submodule.span_le_restrictScalars M.L.O E _ hμ
    have h1 : H.h (a + b) μ ∈ M.L.O := (hsd.2.2 _).1 hab μ (hMM hμ)
    rw [H.h_add_left, hermitian_W0_span_zero H t hb hμU, add_zero] at h1
    exact h1
  have hdec : ∀ (U W : Submodule E V), IsCompl U W → ∀ x : V, ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
    intro U W hUW x
    have hx : x ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.1 hx
  have hperp_a : ∀ {g : Fin (r + 1) → V} (a b : V), b ∈ H.perp (H.X g) → a + b ∈ H.perp (H.X g) →
      a ∈ H.perp (H.X g) := by
    intro g a b hb hab
    have : a = (a + b) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ hab hb

  have hθs : ∀ m₂ : ↥(MMsharp H t₂), ∃ m₁ : ↥(MMsharp H t₁), θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := by
    intro m₂
    obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ m₂))
    refine ⟨m₁, ?_⟩
    rw [show ddMk H t₁ m₁ = θ.symm (ddMk H t₂ m₂) from hm₁, LinearEquiv.apply_symm_apply]
  constructor
  · intro hL
    apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨u₁, hu₁, rfl⟩, rfl⟩
      obtain ⟨n₁, hn₁⟩ := hsurj₁ u₁
      have hx₁p : (u₁ : V) + n₁ ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ n₁.2)
      have hmem : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) ∈ H.Lset Λ₂ g₂ := by
        rw [← hL]
        exact ⟨_, ⟨⟨_, hx₁p⟩, hn₁, rfl⟩, rfl⟩
      obtain ⟨x₂, hx₂Λ, hx₂e⟩ := hmem
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 u₁ (spanMM_le_U H t₁ u₁.2.1) hu₁
      have e1 : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ n₁, hW₂ (ψ n₁).2⟩ := by
        rw [mkW_add H _ _ hu₁ (hW₁ n₁.2), map_add (f := _), hχu, hC1]
      have e2 : H.mkW g₂ x₂ = H.mkW g₂ ⟨a, hap⟩ + H.mkW g₂ ⟨b, hW₂ hb⟩ := by
        rw [← mkW_add H _ _ hap (hW₂ hb)]
        exact mkW_congr H _ _ hab.symm
      have e3 : H.mkW g₂ ⟨a - u', Submodule.sub_mem _ hap hu'p⟩ =
          H.mkW g₂ ⟨(ψ n₁ : V) - b, Submodule.sub_mem _ (hW₂ (ψ n₁).2) (hW₂ hb)⟩ := by
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb), sub_eq_sub_iff_add_eq_add,
          ← e2, hx₂e, e1, add_comm]
      have hb0 := hsep₂ (a - u') ((ψ n₁ : V) - b) (Submodule.sub_mem _ ha hu'U)
        (Submodule.sub_mem _ (ψ n₁).2 hb) (Submodule.sub_mem _ hap hu'p) e3
      have hbψ : b = (ψ n₁ : V) := (sub_eq_zero.1 hb0).symm
      have e4 : H.mkW g₂ ⟨a, hap⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb)] at this
        rw [mkW_congr H (hW₂ (ψ n₁).2) (hW₂ hb) hbψ.symm, sub_self, sub_eq_zero] at this
        exact this
      have hθu : θ (ddMk H t₁ u₁) = ddMk H t₂ ⟨a, haMM⟩ :=
        (hθ u₁ ⟨a, haMM⟩).2 ⟨n₁, hn₁, by rw [← hbψ, hab]; exact hx₂Λ⟩
      refine ⟨⟨a, haMM⟩, hap, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθu, hχu.trans e4.symm⟩
    · rintro _ ⟨u₂, hu₂, rfl⟩
      obtain ⟨m₁, hm₁⟩ := hθs u₂
      obtain ⟨n₁, hn₁, hx₂Λ⟩ := (hθ m₁ u₂).1 hm₁
      have hx₂p : (u₂ : V) + ψ n₁ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ n₁).2)
      have hmem : H.mkW g₂ ⟨(u₂ : V) + ψ n₁, hx₂p⟩ ∈ χ '' H.Lset t₁.abelian₂ g₁ := by
        rw [hL]
        exact ⟨⟨_, hx₂p⟩, hx₂Λ, rfl⟩
      obtain ⟨_, ⟨x₁, hx₁Λ, rfl⟩, hx₁e⟩ := hmem
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 a₁ ha₁ ha₁p
      have e1 : χ (H.mkW g₁ x₁) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ ⟨b₁, hb₁⟩, hW₂ (ψ ⟨b₁, hb₁⟩).2⟩ := by
        rw [mkW_congr H x₁.2 (Submodule.add_mem _ ha₁p (hW₁ hb₁)) hab₁.symm, mkW_add H _ _ ha₁p (hW₁ hb₁),
          map_add, hχu]
        rw [← hC1 ⟨b₁, hb₁⟩]
      have e3 : H.mkW g₂ ⟨(u₂ : V) - u', Submodule.sub_mem _ hu₂ hu'p⟩ =
          H.mkW g₂ ⟨(ψ ⟨b₁, hb₁⟩ : V) - ψ n₁, Submodule.sub_mem _ (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)⟩ := by
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2),
          sub_eq_sub_iff_add_eq_add, ← mkW_add H _ _ hu₂ (hW₂ (ψ n₁).2), ← hx₁e, e1, add_comm]
      have hb0 := hsep₂ ((u₂ : V) - u') ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁)
        (Submodule.sub_mem _ (spanMM_le_U H t₂ u₂.2.1) hu'U)
        (Submodule.sub_mem _ (ψ ⟨b₁, hb₁⟩).2 (ψ n₁).2) (Submodule.sub_mem _ hu₂ hu'p) e3
      have hψeq : ψ ⟨b₁, hb₁⟩ = ψ n₁ := Subtype.ext (sub_eq_zero.1 hb0)
      have hbn : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) = n₁ := ψ.injective hψeq
      have e4 : H.mkW g₂ ⟨u₂, hu₂⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)] at this
        rw [mkW_congr H (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2) (congrArg Subtype.val hψeq), sub_self,
          sub_eq_zero] at this
        exact this
      have hθa : θ (ddMk H t₁ ⟨a₁, ha₁MM⟩) = ddMk H t₂ u₂ :=
        (hθ ⟨a₁, ha₁MM⟩ u₂).2 ⟨⟨b₁, hb₁⟩, by rw [hab₁]; exact hx₁Λ, by rw [hψeq]; exact hx₂Λ⟩
      refine ⟨(ddMk H t₁ ⟨a₁, ha₁MM⟩, H.mkW g₁ ⟨a₁, ha₁p⟩), ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθa, hχu.trans e4.symm⟩
  · intro hG
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x₁, hx₁Λ, rfl⟩, rfl⟩
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      have hin : (θ (ddMk H t₁ ⟨a₁, ha₁MM⟩), χ (H.mkW g₁ ⟨a₁, ha₁p⟩)) ∈ GamG H t₂ g₂ := by
        rw [← hG]
        exact ⟨_, ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, rfl⟩
      obtain ⟨u₂, hu₂, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ ⟨a₁, ha₁MM⟩ u₂).1 hue.1
      have hd : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) - n₁ ∈ {w : ↥(H.W0 t₁.f t₁.f') | (w : V) ∈ t₁.abelian₂} := by
        show b₁ - (n₁ : V) ∈ t₁.abelian₂
        have := t₁.abelian₂.sub_mem hx₁Λ hn₁
        rwa [← hab₁, show a₁ + b₁ - (a₁ + (n₁ : V)) = b₁ - n₁ by abel] at this
      have hdψ := (hth _).1 hd
      rw [map_sub, Submodule.coe_sub] at hdψ
      have hx₂Λ : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ Λ₂ := by
        have := Λ₂.add_mem hx₂' hdψ
        rwa [show (u₂ : V) + ψ n₁ + ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁) = u₂ + ψ ⟨b₁, hb₁⟩ by abel] at this
      have hx₂p : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2)
      refine ⟨⟨_, hx₂p⟩, hx₂Λ, ?_⟩
      rw [mkW_add H _ _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2), ← hC1 ⟨b₁, hb₁⟩, ← hue.2, ← map_add (f := _),
        ← mkW_add H _ _ ha₁p (hW₁ hb₁)]
      exact congrArg χ (mkW_congr H _ _ hab₁)
    · rintro _ ⟨x₂, hx₂Λ, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      have hin : (ddMk H t₂ ⟨a, haMM⟩, H.mkW g₂ ⟨a, hap⟩) ∈
          (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ := by
        rw [hG]
        exact ⟨⟨a, haMM⟩, hap, rfl⟩
      obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ u₁ ⟨a, haMM⟩).1 hue.1
      set bb : ↥(H.W0 t₁.f t₁.f') := ψ.symm ⟨b, hb⟩
      have hψbb : (ψ bb : V) = b := by simp [bb]
      have hd2 : (ψ (bb - n₁) : V) ∈ Λ₂ := by
        rw [map_sub, Submodule.coe_sub, hψbb]
        have := Λ₂.sub_mem hx₂Λ hx₂'
        rwa [← hab, show a + b - (a + (ψ n₁ : V)) = b - ψ n₁ by abel] at this
      have hd1 : ((bb - n₁ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ t₁.abelian₂ := (hth _).2 hd2
      have hx₁Λ : (u₁ : V) + bb ∈ t₁.abelian₂ := by
        have := t₁.abelian₂.add_mem hn₁ hd1
        rwa [Submodule.coe_sub, show (u₁ : V) + n₁ + ((bb : V) - n₁) = u₁ + bb by abel] at this
      have hx₁p : (u₁ : V) + bb ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ bb.2)
      refine ⟨_, ⟨⟨_, hx₁p⟩, hx₁Λ, rfl⟩, ?_⟩
      rw [mkW_add H _ _ hu₁ (hW₁ bb.2), map_add (f := _), hue.2, hC1]
      rw [← mkW_add H _ _ hap (hW₂ (ψ bb).2)]
      exact mkW_congr H _ _ (by rw [hψbb, hab])

end CR

end Formalism.L2.SG.LsDatumA
end
end

