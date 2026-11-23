module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem bwL_descent (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E)
    (he : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.inclE (F := F) (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AF F) e ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.SS F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨D, hD, hDe⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  set d : E := algebraMap F E (D : F) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; intro h
    exact hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))
  have hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range := by
    intro k
    have := hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)
    rwa [Algebra.smul_def] at this
  let f : 𝓞 E →ₗ[ℤ] E := LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
  have hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    obtain ⟨y, hy⟩ := hpow k
    exact ⟨y, by simp [f, hy, hd0]⟩
  have : IsNoetherian ℤ (LinearMap.range f) := by
    exact isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have : IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule := isNoetherian_of_le hS
  have hint : IsIntegral ℤ e :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e
      (Algebra.subset_adjoin (Set.mem_singleton e))
  exact ⟨⟨e, hint⟩, rfl⟩

variable (D : D7) (u : D.what₂.Word)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bwL_lcInt (Tt : FormsTied D u) : BwLcInt D u := by
  intro i hi c x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat ((Tt.cls i hi).y c).1 (Tt.cls i hi).lev.Lb := by
    intro z hz
    exact ((Tt.cls i hi).y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ (Tt.cls i hi).lev.Lb, ∀ b ∈ (Tt.cls i hi).lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := (Tt.cls i hi).lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) (Tt.cls i hi).lev.Lb 1 hm ((Tt.cls i hi).y c).1
    ((Tt.cls i hi).y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical IsDedekindDomain

theorem bwG_span_dualSet {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) :
    ((Submodule.span (𝓞 K) (dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = dualSet σ J L := by
  apply le_antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero =>
      intro x _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add y y' _ _ hy hy' =>
      intro x hx
      have e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
        simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem (hy x hx) (hy' x hx)
    | smul r y _ hy =>
      intro x hx
      have e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact mul_mem ⟨r, rfl⟩ (hy x hx)
  · exact Submodule.subset_span

variable (D : D7) (u : D.what₂.Word)

theorem bwG_Ld_coe (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (Ld D u i hi c : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c) :=
  bwG_span_dualSet _ _ _

theorem bwG_intSpan_smul (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) {Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    D.what₂.embLL r • Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  induction hQ using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * s, f, mul_mem hr hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem bwG_int_mem (w : D.what₂.places.Pl) (k : 𝓞 D.what₂.LL) :
    algebraMap (𝓞 D.what₂.LL) D.what₂.LL k ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one k)

theorem bwG_inv_mem (w : D.what₂.places.Pl) {r : 𝓞 D.what₂.LL} (hr : r ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ ∈ intW D.what₂.places w := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hr
  exact (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PDnDil
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DdlGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}


end DdlGen

section DdlLoc

variable {E : Type} [Field E] [NumberField E]

theorem ddl_mulLat_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.one_mulVec]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem localization_inv_smul_eq {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A) = Formalism.HermitianLatticesTheory.localization₂ P B) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  rw [← rlv_mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ddl_mulLat_one] at k1 k2
  exact le_antisymm k1 k2

variable {E : Type} [Field E] [NumberField E]

theorem localization_mono₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M N : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP _ _ _).1 hx
  exact (rlv_mem_locP _ _ _).2 ⟨s, hs, h hsx⟩

theorem mem_localization_of_mem₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (h : x ∈ M) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P M :=
  (rlv_mem_locP _ _ _).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact h⟩

theorem localization_smul_cancel {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g g' : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g' : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A)) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ * g' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have e1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← rlv_mulLat_mul, ← rlv_mulLat_mul, e1, ddl_mulLat_one, ← Units.val_mul] at k1 k2
  exact le_antisymm k1 k2

end DdlLoc

section DdlTied

variable {D : D7} {u : D.what₂.Word}








end DdlTied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocW
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DualQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rlv_dualQ {n : ℕ} (σ : E →ₐ[F] E) (hσσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E)
    (hH : ∀ u w, hform (σ : E →+* E) J w u = σ (hform (σ : E →+* E) J u w))
    (g : Matrix (Fin n) (Fin n) E) (hg : cT (σ : E →+* E) g * J * g = J)
    (P : Ideal (𝓞 E)) [P.IsPrime] {A B : Submodule (𝓞 E) (Fin n → E)}
    (hBfg : (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B).FG)
    (hBB : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ B)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) ≤ Formalism.HermitianLatticesTheory.localization₂ P (mulLat g (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J A))) :
    Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) (mulLat g A) ≤
      Formalism.HermitianLatticesTheory.localization₂ (P.comap (RingOfIntegers.mapRingHom (σ : E →+* E))) B := by
  classical
  have hP1 : (1 : 𝓞 E) ∉ P := P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance)
  intro x hx
  obtain ⟨t0, ht0, hx0⟩ := (rlv_mem_locP _ _ _).1 hx
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.1 hx0
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hax
  have key : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, ∃ s : 𝓞 E, s ∉ P ∧
      (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 (hP ((rlv_mem_locP _ _ _).2 ⟨1, hP1, by rw [one_smul]; exact hy⟩))
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hwy
    refine ⟨s, hs, ?_⟩
    have e1 : (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y = hform (σ : E →+* E) J (g *ᵥ a) (s • y) := by
      rw [← algebraMap_smul E s y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
    rw [e1, ← hwy, Formalism.UG.P.hform_mulVec, hg]
    exact (Formalism.L2.GlobalTheoryTheory.Comp.mem_dl σ J A w).1 hw a ha
  choose! sf hsfP hsf using key
  obtain ⟨S, hS⟩ := hBfg
  have hSsub : ∀ y ∈ S, y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B := fun y hy => hS ▸ Submodule.subset_span hy
  set s : 𝓞 E := ∏ y ∈ S, sf y with hsdef
  have hsP : s ∉ P := by
    rw [hsdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨y, hy, hyP⟩
    exact hsfP y (hSsub y hy) hyP
  have hgen : ∀ y ∈ S, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [hsdef, ← Finset.mul_prod_erase S sf hy]
    obtain ⟨r, hr⟩ := hsf y (hSsub y hy)
    refine ⟨(∏ z ∈ S.erase y, sf z) * r, ?_⟩
    rw [map_mul, hr]
    push_cast
    ring
  have hall : ∀ y ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B, (s : E) * hform (σ : E →+* E) J (g *ᵥ a) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_zero_right, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_add_right, mul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul E r y, Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right]
      obtain ⟨q, hq⟩ := hy
      exact ⟨r * q, by rw [map_mul, hq]; ring⟩
  set s' : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) s with hs'def
  have hs'E : (s' : E) = σ (s : E) := rfl
  have hmem : s' • (g *ᵥ a) ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J B) := by
    apply Submodule.subset_span
    intro y hy
    have e2 : hform (σ : E →+* E) J y (s' • (g *ᵥ a)) = σ ((s : E) * hform (σ : E →+* E) J (g *ᵥ a) y) := by
      rw [← algebraMap_smul E s' (g *ᵥ a), Formalism.L2.GlobalTheoryTheory.Comp.hform_smul_right, hH, map_mul]
      rfl
    rw [e2]
    obtain ⟨q, hq⟩ := hall y hy
    exact ⟨RingOfIntegers.mapRingHom (σ : E →+* E) q, by rw [← hq]; rfl⟩
  refine (rlv_mem_locP _ _ _).2 ⟨s' * t0, ?_, ?_⟩
  · intro hm
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hm) with h1 | h1
    · apply hsP
      have : RingOfIntegers.mapRingHom (σ : E →+* E) s' = s := by
        apply RingOfIntegers.ext
        show σ (σ (s : E)) = (s : E)
        exact hσσ _
      rw [← this]
      exact h1
    · exact ht0 h1
  · rw [mul_smul, ← hax]
    exact hBB hmem

end DualQ

section TiedQ

variable {D : D7} {u : D.what₂.Word}

theorem rlv_sig_sig (x : D.host.E) : sigD D (sigD D x) = x := by
  rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]


set_option maxHeartbeats 2000000 in
theorem rlv_coordFacts (i : ℕ) (hi : i ≤ D.R.m) :
    (∀ c, Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) =
      clsCrd D u i hi c) ∧
    (∀ c, (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)).FG) ∧
    (∀ a b, hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) b a =
      sigD D (hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b)) := by
  letI := D.host.cmStar
  set κ : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) with hκ
  have hform_eq : ∀ x y, (D.sp.X i).hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (κ x) (κ y) := by
    intro x y
    have hx : (D.sp.X i).hT x y = ∑ a, ∑ b, star ((D.sp.X i).frame.repr x a) * (D.sp.X i).gram a b *
        (D.sp.X i).frame.repr y b := by
      conv_lhs => rw [← (D.sp.X i).frame.sum_repr x, ← (D.sp.X i).frame.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, HSpace.gram, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [RingHom.id_apply]
      ring
    rw [hx]
    unfold hform
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (finCongr (rankN D i hi)).symm.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [gramN, hκ, CMData.sig, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, starRingEnd_apply]
  let K : Formalism.L2.GlobalTheoryTheory.Comp.Coord D.sp.cm (D.sp.X i) (Fin (D.R.N i)) := ⟨κ, gramN D i hi, hform_eq⟩
  have hdual c := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (D.sp.X i).V
    (D.sp.X i).hT (D.sp.X i).herm (D.sp.X i).nondeg
    Formalism.L2.GlobalTheoryTheory.Comp.star_int (D.clsLat u i c) (D.clsLat_lat u i c)
  refine ⟨fun c => ?_, fun c => ?_, fun a b => ?_⟩
  · have e1 := K.lat_dual (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))
    have e2 := K.lat_dual (D.clsLat u i c)
    rw [(hdual c).2.1, e2] at e1
    exact e1.symm
  · have hfg : (K.lat (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c))).FG :=
      (hdual c).1.toIsLattice.fg.map _
    rw [K.lat_dual] at hfg
    exact hfg
  · have h := (D.sp.X i).herm.eq (κ.symm a) (κ.symm b)
    rw [hform_eq, hform_eq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm


end TiedQ

section TiedW

variable {D : D7} {u : D.what₂.Word}





end TiedW

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

