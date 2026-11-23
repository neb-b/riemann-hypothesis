module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGP
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem prim_comp {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {Λ : Submodule M.L.O V} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {v : ι → V} (hv : H.Prim Λ v)
    (e : κ → ι) (he : Function.Injective e) : H.Prim Λ (v ∘ e) := by
  refine ⟨fun a => hv.1 (e a), hv.2.1.comp e he, fun x hx hxs => ?_⟩
  have hxv : x ∈ Submodule.span E (Set.range v) := Submodule.span_mono (Set.range_comp_subset_range e v) hxs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hv.2.2 x hx hxv)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have ha' : ∑ i, ((a i : M.L.O) : E) • v i = x := ha
  let d' : ι → E := fun i => ∑ j, if e j = i then d j else 0
  have hd' : ∑ i, d' i • v i = ∑ j, d j • v (e j) := by
    simp only [d', Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_eq]
    simp
  have hcoef : ∀ i, ((a i : M.L.O) : E) = d' i := by
    have h0 : ∑ i, (((a i : M.L.O) : E) - d' i) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hd', ha']
      simpa using hd.symm ▸ sub_self x
    intro i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv.2.1 _ h0 i)
  have hzero : ∀ i, i ∉ Set.range e → a i = 0 := by
    intro i hi
    apply Subtype.ext
    rw [hcoef i]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hi ⟨j, h⟩)]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => a (e j), ?_⟩
  rw [← ha]
  exact (Fintype.sum_of_injective e he (fun j => a (e j) • (v ∘ e) j) (fun i => a i • v i)
    (fun i hi => by rw [hzero i hi, zero_smul]) (fun j => rfl))

theorem genOfPrim_holds (M : Model F E) (r n : ℕ) : GenOfPrim M r n := by
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂ Λ₂ hsd hprim
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hnt : Nontrivial E := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    have h0 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    rw [M.L.rank] at h0
    exact absurd h0 (by norm_num)
  have hfam_inl : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inl = f₂ := by
    funext a
    unfold HermSp.MMfam
    rcases M.split with _ | g <;> rfl
  have hPf : H.Prim Λ₂ f₂ := by
    have := prim_comp H hprim Sum.inl Sum.inl_injective
    rwa [hfam_inl] at this
  have hPf' : H.Prim Λ₂ f₂' := by
    rcases hs : M.split with _ | g
    · have hfam_inr : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inr = f₂' := by
        funext a
        unfold HermSp.MMfam
        rw [hs]
        rfl
      have := prim_comp H hprim Sum.inr Sum.inr_injective
      rwa [hfam_inr] at this
    · set Q : E := algebraMap F E (g.q : F)
      set qi : E := algebraMap F E ((g.q : F)⁻¹)
      have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
      have hQqi : Q * qi = 1 := by
        simp only [Q, qi]
        rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
      have hQO : Q ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
      have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
        unfold HermSp.MMfam
        rw [hs]
      rw [hMM] at hprim
      obtain ⟨hmem, hli, hsat⟩ := hprim
      set y : Fin (r + 1) → V := fun a => qi • (f₂' a - f₂ a)
      have hf' : ∀ a, f₂' a = f₂ a + Q • y a := by
        intro a
        simp only [y]
        rw [smul_smul, hQqi, one_smul]
        abel
      refine ⟨fun a => ?_, ?_, fun x hx hxs => ?_⟩
      · rw [hf' a]
        refine Submodule.add_mem _ (hmem (Sum.inl a)) ?_
        have := Λ₂.smul_mem (⟨Q, hQO⟩ : M.L.O) (hmem (Sum.inr a))
        rwa [Subring.smul_def] at this
      · rw [Fintype.linearIndependent_iff]
        intro d hd a
        have h0 : ∑ i, (Sum.elim d (fun b => d b * Q) i) • Sum.elim f₂ y i = 0 := by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [← hd, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hf' b, smul_add, mul_smul]
        exact (Fintype.linearIndependent_iff.1 hli) _ h0 (Sum.inl a)
      · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
        have hx2 : ∑ a, d a • f₂' a ∈ Submodule.span E (Set.range (Sum.elim f₂ y)) := by
          refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
          rw [hf' a]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩))
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hsat _ hx hx2)
        have hcoef := (Fintype.linearIndependent_iff.1 hli)
          (fun i => (c i : E) - Sum.elim d (fun b => d b * Q) i) (by
            simp only [sub_smul, Finset.sum_sub_distrib]
            have e1 : ∑ i, (c i : E) • Sum.elim f₂ y i = ∑ a, d a • f₂' a := by
              rw [← hc]
              exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
            rw [e1, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [← Finset.sum_add_distrib, sub_eq_zero]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hf' b, smul_add, mul_smul])
        have hdO : ∀ a, d a ∈ M.L.O := by
          intro a
          have := hcoef (Sum.inl a)
          simp only [Sum.elim_inl] at this
          rw [← sub_eq_zero.1 this]
          exact (c _).2
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem (Submodule.span M.L.O (Set.range f₂')) (⟨d a, hdO a⟩ : M.L.O)
          (Submodule.subset_span ⟨a, rfl⟩)
        rwa [Subring.smul_def] at this
  refine ⟨⟨hsd, ⟨hPf, hF₂.1, hF₂.2, hT1.2.1.2.2.2⟩, ⟨hPf', hF₂'.1, hF₂'.2, hT1.2.2.1.2.2.2⟩, hD₂, hG₂.ne_zero,
    fun g hs => ⟨(hT1.2.2.2.2.2 g hs).1, (hT1.2.2.2.2.2 g hs).2.1, fun b => ?_⟩⟩, hprim⟩
  have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
      Sum.elim f₂ (fun a => algebraMap F E ((g.q : F)⁻¹) • (f₂' a - f₂ a)) := by
    unfold HermSp.MMfam
    rw [hs]
  have hy : algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b) ∈ Λ₂ := by
    have := hprim.1 (Sum.inr b)
    rw [hMM] at this
    exact this
  have e : f₂' b - f₂ b = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b)) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul]
  show f₂' b - f₂ b ∈ H.smulLat (algebraMap F E (g.q : F)) Λ₂
  rw [e]
  exact Submodule.subset_span ⟨_, hy, rfl⟩

end GP

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SignTransposeTwisted
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Theta

variable {K : Type*} [CommRing K] {r : ℕ}

theorem signMatrix_transpose : (Sg K r).transpose = Sg K r := Matrix.diagonal_transpose _

theorem theta_mul (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M * N).transpose * Sg K r = (Sg K r * N.transpose * Sg K r) * (Sg K r * M.transpose * Sg K r) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Sg K r) (Sg K r), sg_sq, Matrix.one_mul]

theorem theta_theta (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Sg K r * M.transpose * Sg K r).transpose * Sg K r = M := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, signMatrix_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [sg_sq, Matrix.mul_one, ← Matrix.mul_assoc, sg_sq, Matrix.one_mul]

theorem theta_stab {a Y b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : a * Y * b = Y) :
    (Sg K r * b.transpose * Sg K r) * (Sg K r * Y.transpose * Sg K r) * (Sg K r * a.transpose * Sg K r) =
      Sg K r * Y.transpose * Sg K r := by
  rw [← theta_mul, ← theta_mul, ← Matrix.mul_assoc, h]

theorem theta_sub_one (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M - 1).transpose * Sg K r = Sg K r * M.transpose * Sg K r - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sg_sq]

theorem theta_lo {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUp U) : IsLo (Sg K r * U.transpose * Sg K r) :=
  isLo_conj (isLo_transpose h) _ _ (fun a => sgn_sq' r a)

theorem theta_up {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLo L) : IsUp (Sg K r * L.transpose * Sg K r) :=
  isUp_conj (isUp_transpose h) _ _ (fun a => sgn_sq' r a)

theorem neg_one_pow_mem (J : AddSubgroup K) (k : ℕ) {x : K} (hx : x ∈ J) : (-1 : K) ^ k * x ∈ J := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [neg_one_mul]; exact J.neg_mem hx

theorem ent_theta {J : AddSubgroup K} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : EntIn J M) :
    EntIn J (Sg K r * M.transpose * Sg K r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [mul_comm]
  exact neg_one_pow_mem J _ (neg_one_pow_mem J _ (h j i))

theorem sign_transpose_twisted (s e : K) (cf : Fin (r + 1) → K) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (s • (Matrix.diagonal cf * (Z.transpose * Sg K r) * Matrix.diagonal cf) - e • Ecorner r).transpose *
      Sg K r = s • (Matrix.diagonal cf * (Z * Sg K r) * Matrix.diagonal cf) - e • Ecorner r := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Ecorner, Matrix.of_apply]
  have hs := sgn_sq' (R := K) r
  by_cases hij : i = Fin.last r ∧ j = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · have hji : ¬ (j = Fin.last r ∧ i = Fin.last r) := fun h => hij ⟨h.2, h.1⟩
    rw [if_neg hij, if_neg hji]
    linear_combination (s * cf i * cf j * Z i j * (-1 : K) ^ (r - j.val)) * hs i

theorem theta_move (cf cfi : Fin (r + 1) → K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Matrix.diagonal cfi * (Sg K r * A.transpose * Sg K r) * Matrix.diagonal cf).transpose * Sg K r =
      Matrix.diagonal cf * A * Matrix.diagonal cfi := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hs := sgn_sq' (R := K) r
  linear_combination (cf i * A i j * cfi j * (-1 : K) ^ (r - j.val) * (-1 : K) ^ (r - j.val)) * hs i +
    (cf i * A i j * cfi j) * hs j

end Theta

section ModelR

variable {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [CommRing Ep] [Algebra Fp Ep]
  [TopologicalSpace Ep] [MeasurableSpace Ep]

theorem mem_R_of (M : Formalism.MainNotions.S.Loc.Model Fp Ep) (g : Formalism.MainNotions.S.Loc.SplitG M.L) (hM : M.split = some g) (x : Ep)
    (h1 : (g.e x).1 ∈ 𝒪[Fp]) (h2 : (g.e x).2 ∈ 𝒪[Fp])
    (h3 : ∃ t ∈ 𝒪[Fp], (g.e x).1 - (g.e x).2 = (g.q : Fp) * t) : x ∈ M.R := by
  obtain ⟨L, sp, mu⟩ := M
  change Formalism.MainNotions.S.Loc.SplitG L at g
  obtain rfl : sp = some g := hM
  exact (Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x).2 ⟨h1, h2, h3⟩

end ModelR

section Place

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem ptMat_mono' (w : Point D.host.E (D.R.rS + 1)) : ptMat w = mono (fσ w) (fun a => pv w.1 a) := by
  ext a b
  rw [ptMat_fσ]
  rfl

def gX (L₁ X' : PairVal.MatR D) : PairVal.MatR D := L₁ * X' * L₁⁻¹

def gY (w : Point D.host.E (D.R.rS + 1)) (U₁ X' : PairVal.MatR D) : PairVal.MatR D :=
  U₁⁻¹ * (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹ * U₁

theorem glob_stab (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) :
    IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧
      gX L₁ X' * (Z₁ * Sg D.host.E D.R.rS) * gY w U₁ X' = Z₁ * Sg D.host.E D.R.rS := by
  have hν : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hdc : IsUnit (cOf (fσ w) (fun a => pv w.1 a) X').det := by rw [det_up' hc]; exact isUnit_one
  have hdL : IsUnit L₁.det := by rw [det_lo' hL₁]; exact isUnit_one
  have hdU : IsUnit U₁.det := by rw [det_up' hU₁]; exact isUnit_one
  refine ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, ?_⟩
  have hfix := fix_cOf (fσ_fσ w) (fun a => pv w.1 a) hν X'
  rw [hZ, ptMat_mono']
  simp only [gX, gY, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁⁻¹ L₁, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul, ← Matrix.mul_assoc U₁ U₁⁻¹,
    Matrix.mul_nonsing_inv _ hdU, Matrix.one_mul, ← Matrix.mul_assoc X' (mono (fσ w) (fun a => pv w.1 a)), hfix,
    Matrix.mul_assoc (mono (fσ w) (fun a => pv w.1 a)),
    ← Matrix.mul_assoc (cOf (fσ w) (fun a => pv w.1 a) X') (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹,
    Matrix.mul_nonsing_inv _ hdc, Matrix.one_mul]

theorem locL_lo (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsLo (locL Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locL, hM]
  · exact isLo_conj (isLo_map _ hA) _ _ (fun a => by simp only [← map_mul, cf_cfi, map_one])
  · exact isLo_glue _ (isLo_conj (isLo_map _ hA) _ _ (cf_cfi Zd p))
      (isLo_conj (theta_lo (isUp_map _ hB)) _ _ (cf_cfi Zd p))

theorem locR_up (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsUp (locR Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locR, hM]
  · exact isUp_conj (isUp_map _ hB) _ _ (fun a => by simp only [← map_mul, cfi_cf, map_one])
  · exact isUp_glue _ (isUp_conj (isUp_map _ hB) _ _ (cfi_cf Zd p))
      (isUp_conj (theta_up (isLo_map _ hA)) _ _ (cfi_cf Zd p))

theorem key_stab (p : PlF D) {l ρ L R Yp : MatP D p} (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : L * Yp * R = l * Yp * ρ) : (l⁻¹ * L) * Yp * (R * ρ⁻¹) = Yp := by
  obtain ⟨-, hll, -⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨-, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  calc (l⁻¹ * L) * Yp * (R * ρ⁻¹) = l⁻¹ * (L * Yp * R) * ρ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Yp := by
      rw [h]
      simp only [Matrix.mul_assoc]
      rw [hρρ, Matrix.mul_one, ← Matrix.mul_assoc, hll, Matrix.one_mul]

theorem corr_move (u u' : D.what₂.Word) (p : PlF D) {Z₁ A₀ B₀ X Y : PairVal.MatR D} (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX : IsLo X) (hY : IsUp Y) (hst : X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS) :
    locL Zd p (A₀ * X) (Y * B₀) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
        locR Zd p (A₀ * X) (Y * B₀) =
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ := by
  have h2 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ := by
    rw [Matrix.mul_assoc (A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀), sg_sq, Matrix.mul_one]
  have h3 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      (A₀ * X) * (Z₁ * Sg D.host.E D.R.rS) * (Y * B₀) := by
    rw [h2]
    conv_lhs => rw [← hst]
    simp only [Matrix.mul_assoc]
  exact (locMove Zd u u' p (isLo_mul hA₀ hX) (isUp_mul hY hB₀) h3).symm.trans (locMove Zd u u' p hA₀ hB₀ h2)

theorem locL_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locL Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
      A.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
  simp only [locL, hM]

theorem locR_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locR Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) *
      B.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := by
  simp only [locR, hM]

section Typed

variable (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
  {e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp} (hge : g.e = e)
include hM hge

theorem leftLocal_firstProj (A B : PairVal.MatR D) : (locL Zd p A B).map (p1 e) =
    Matrix.diagonal (cf Zd p) * A.map ((p1 e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p) := by
  simp only [locL, hM, hge, glue_map_fst]

theorem rightLocal_secondProj (A B : PairVal.MatR D) : (locR Zd p A B).map (p2 e) =
    Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 e).comp (D.s.atP p).ιE)).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p) := by
  simp only [locR, hM, hge, glue_map_snd]

end Typed

end Place

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

