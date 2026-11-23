module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongGrpIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem one_quot_apply {n : ℕ} (I : Ideal (AE D)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AE D ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

theorem mem_congGrp_iff {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔
      ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  simp only [GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff, Units.val_one]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [one_quot_apply] at this
    exact Ideal.Quotient.eq.1 this
  · intro h
    ext i j
    rw [one_quot_apply]
    exact Ideal.Quotient.eq.2 (h i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

open GlobalTheory.FinPl in
theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

open GlobalTheory.FinPl in
theorem idOff_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) : idOff D P ≤ idOff D Q := by
  intro a ha
  simp only [idOff, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_le_idOff {P Q : Pl D → Prop} (h : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_inf_idOff {P Q R : Pl D → Prop} (h : ∀ w, P w → ¬ Q w → R w) : idAt D P ⊓ idOff D Q ≤ idAt D R := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  refine ⟨ha.1.1, fun w => ?_⟩
  by_cases hq : Q w.1
  · exact ha.2 ⟨w.1, hq⟩
  · exact ha.1.2 ⟨w.1, fun hp => w.2 (h _ hp hq)⟩

theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : GlobalTheory.FinPl.congGrp V I ≤ GlobalTheory.FinPl.congGrp V J :=
  fun _ hg => mem_congGrp_iff.2 fun i j => h (mem_congGrp_iff.1 hg i j)

theorem congGrp_inf {V : HSp D} {I J : Ideal (AE D)} {g : GA D V} (hI : g ∈ GlobalTheory.FinPl.congGrp V I)
    (hJ : g ∈ GlobalTheory.FinPl.congGrp V J) : g ∈ GlobalTheory.FinPl.congGrp V (I ⊓ J) :=
  mem_congGrp_iff.2 fun i j => ⟨mem_congGrp_iff.1 hI i j, mem_congGrp_iff.1 hJ i j⟩

theorem mul_sub_mem {I : Ideal (AE D)} {k m n : ℕ} {M : Matrix (Fin m) (Fin m) (AE D)}
    (hM : ∀ i j, M i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ I) (N : Matrix (Fin k) (Fin m) (AE D))
    (Y : Matrix (Fin m) (Fin n) (AE D)) (i : Fin k) (j : Fin n) : (N * M * Y - N * Y) i j ∈ I := by
  have e : N * M * Y - N * Y = N * (M - 1) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [e]
  simp only [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_)
  simpa only [Matrix.sub_apply] using hM q l

variable {W : HSp D} {ρ : ℕ}

theorem off_left {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hg' : g' ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W gv⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hg')) (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (Formalism.L2.Theta.mt W gv⁻¹ * X) i j
  simp only [Matrix.one_mul] at h1
  have e : Formalism.L2.Theta.mt W gv⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * (Formalism.L2.Theta.mt W gv⁻¹ * X) - Formalism.L2.Theta.mt W gv⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem off_right {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hgv : gv ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W g'⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hgv)) (Formalism.L2.Theta.mt W g'⁻¹) X i j
  have e : Formalism.L2.Theta.mt W g'⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * Formalism.L2.Theta.mt W gv⁻¹ * X - Formalism.L2.Theta.mt W g'⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem mxOff_mono {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, Q w → P w) {m n : ℕ} {y : Mx D m n} (hy : MxOff P y) :
    MxOff Q y := fun i j => idOff_mono h (hy i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem assemble (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (A : AddSubgroup (Mx D W.rank ρ)) (K : Subgroup (GA D W))
    (t : Finset (GlobalTheory.FinPl.Pl D)) (ht : t.Nonempty)
    (loc : ∀ v ∈ t, ∀ g ∈ grpAt W (· = v),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· = v) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) :
    ∀ g ∈ grpAt W (· ∈ t),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· ∈ t) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ t) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ t) ∧ g = r * k := by
  revert loc
  induction ht using Finset.Nonempty.cons_induction with
  | singleton v =>
    intro loc g hg hc
    simp only [Finset.mem_singleton] at hg hc loc ⊢
    exact loc v rfl g hg hc
  | cons v t hv ht ih =>
    intro loc g hg hc
    obtain ⟨u, a, ha, hc⟩ := hc
    obtain ⟨gv, hgv, g', hg', rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have hcomm := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1
    have hsub : ∀ w, w ∈ t → ¬ (w = v) := fun w hw e => hv (e ▸ hw)
    have hvt : grpAt W (· = v) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => hw ▸ Finset.mem_cons_self v t)
    have htt : grpAt W (· ∈ t) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => Finset.mem_cons.2 (Or.inr hw))
    have ht_off : grpAt W (· ∈ t) ≤ grpOff W (· = v) :=
      congGrp_mono (idAt_le_idOff fun w hw hwt => hsub w hwt hw)
    have hv_off : grpAt W (· = v) ≤ grpOff W (· ∈ t) :=
      congGrp_mono (idAt_le_idOff fun w hw hwv => hsub w hw hwv)
    have hg'1 : g' ∈ grpAt W (· ∈ t) := by
      have h1 : g' ∈ grpAt W (· ∈ Finset.cons v t hv) := by
        have := mul_mem (inv_mem (hvt hgv)) hg
        rwa [inv_mul_cancel_left] at this
      exact congGrp_mono (idAt_inf_idOff fun w hw hnv => (Finset.mem_cons.1 hw).resolve_left hnv)
        (congGrp_inf h1 hg')
    have hcv : MxOff (· = v) (Formalism.L2.Theta.mt W gv⁻¹ * (x * u.1.1) - x - a) :=
      off_left hg' (mxOff_mono (fun w hw => hw ▸ Finset.mem_cons_self v t) hc)
    have hct : MxOff (· ∈ t) (Formalism.L2.Theta.mt W g'⁻¹ * (x * u.1.1) - x - a) :=
      off_right (hv_off hgv) (mxOff_mono (fun w hw => Finset.mem_cons.2 (Or.inr hw)) hc)
    obtain ⟨rv, hrv, hrv', kv, hkv, hkv', rfl⟩ := loc v (Finset.mem_cons_self v t) gv hgv ⟨u, a, ha, hcv⟩
    obtain ⟨r', hr', hr'', k', hk', hk'', rfl⟩ :=
      ih (fun w hw => loc w (Finset.mem_cons.2 (Or.inr hw))) g' hg'1 ⟨u, a, ha, hct⟩
    refine ⟨rv * r', mul_mem hrv hr', mul_mem (hvt hrv') (htt hr''), kv * k', mul_mem hkv hk',
      mul_mem (hvt hkv') (htt hk''), ?_⟩
    have hc' := hcomm kv hkv' r' (ht_off hr'')
    calc rv * kv * (r' * k') = rv * (kv * r') * k' := by simp only [mul_assoc]
      _ = rv * (r' * kv) * k' := by rw [hc']
      _ = rv * r' * (kv * k') := by simp only [mul_assoc]

end GlobalTheory.OneCosetBF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)

noncomputable section
namespace GlobalTheory.RatLat

theorem dual_gens {A K W : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W] (M : Submodule A W)
    (hfg : M.FG) (hden : ∀ v : W, ∃ d : A, d ≠ 0 ∧ d • v ∈ M) :
    ∃ (m : ℕ) (g : Fin m → W) (Φ : Fin m → W →ₗ[K] K), (∀ i, g i ∈ M) ∧
      (∀ i, ∀ x ∈ M, Φ i x ∈ (algebraMap A K).range) ∧ ∀ x, x = ∑ i, Φ i x • g i := by
  classical
  haveI hfin : Module.Finite A M := Module.Finite.iff_fg.2 hfg
  have hcancel : ∀ (d : A) (x : W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd)
  haveI hflat : Module.Flat A M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : A) • (x : W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  haveI hfp : Module.FinitePresentation A M := Module.finitePresentation_of_finite _ _
  haveI hproj : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin m → W := fun i => (π (Pi.single i 1) : W)
  have hg : ∀ i, g i ∈ M := fun i => (π (Pi.single i 1)).2
  have hexp : ∀ x : M, (x : W) = ∑ i, (algebraMap A K (σ x i)) • g i := by
    intro x
    have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
    conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ π (σ x)]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, IsScalarTower.algebraMap_smul]
    congr 2
    congr 1
    funext j
    simp [Pi.single_apply, eq_comm]
  have hsp : Submodule.span K (M : Set W) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨d, hd, hv⟩ := hden v
    have hd' : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd
    have : v = (algebraMap A K d)⁻¹ • (d • v) := by
      rw [← IsScalarTower.algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  have hunitW : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A W) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) W K).map_units
  have hunitK : ∀ x : nonZeroDivisors A, IsUnit (algebraMap A (Module.End A K) x) :=
    (isLocalizedModule_id (nonZeroDivisors A) K K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors A) M.subtype := by
    refine ⟨hunitW, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let φ : Fin m → M →ₗ[A] K := fun i => (Algebra.linearMap A K) ∘ₗ (LinearMap.proj i) ∘ₗ σ
  let Φ0 : Fin m → W →ₗ[A] K := fun i => IsLocalizedModule.lift (nonZeroDivisors A) M.subtype (φ i) hunitK
  have hΦ0 : ∀ i (x : M), Φ0 i (x : W) = algebraMap A K (σ x i) := fun i x =>
    IsLocalizedModule.lift_apply _ M.subtype (φ i) hunitK x
  let Φ : Fin m → W →ₗ[K] K := fun i => (Φ0 i).extendScalarsOfIsLocalization (nonZeroDivisors A) K
  have hΦ : ∀ i (x : M), Φ i (x : W) = algebraMap A K (σ x i) := fun i x => hΦ0 i x
  refine ⟨m, g, Φ, hg, fun i x hx => ⟨σ ⟨x, hx⟩ i, (hΦ i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hL : (LinearMap.id : W →ₗ[K] W) = ∑ i, (LinearMap.smulRight (Φ i) (g i)) := by
    refine LinearMap.ext_on hsp fun y hy => ?_
    rw [LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    refine (hexp ⟨y, hy⟩).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (· • g i) (hΦ i ⟨y, hy⟩).symm
  have := LinearMap.congr_fun hL x
  simpa using this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem coe_mem_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (f : F) :
    algebraMap F (Fv F v) f ∈ v.adicCompletionIntegers F ↔ v.valuation F f ≤ 1 := by
  rw [mem_adicCompletionIntegers]
  exact Iff.of_eq (congrArg (· ≤ 1) (valuedAdicCompletion_eq_valuation' v f))

theorem int_of_intAf {F : Type} [Field F] [NumberField F] (f : F) (h : algebraMap F (Af F) f ∈ intAf F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine mem_integers_of_valuation_le_one F f fun v => ?_
  have := h v
  rw [AlgHom.commutes] at this
  exact (coe_mem_int_iff v f).1 this

theorem smul_intAf {F : Type} [Field F] [NumberField F] (c : 𝓞 F) {α : Af F} (hα : α ∈ intAf F) :
    (algebraMap (𝓞 F) F c) • α ∈ intAf F := by
  intro v
  rw [map_smul, Algebra.smul_def]
  refine mul_mem ((coe_mem_int_iff v _).2 (valuation_le_one v c)) (hα v)

def extF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) : AF F ⊗[F] E →ₗ[F] AF F :=
  (TensorProduct.rid F (AF F)).toLinearMap ∘ₗ LinearMap.lTensor (AF F) ψ

theorem extF_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (ψ : E →ₗ[F] F) (a : AF F) (e : E) :
    extF ψ (a ⊗ₜ[F] e) = ψ e • a := by
  simp [extF]

def extV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : AF F :=
  ∑ j, extF (Φ ∘ₗ LinearMap.single F (fun _ : Fin n => E) j) (y j)

theorem extV_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (a : AF F) (x : Fin n → E) : extV Φ (fun i => a ⊗ₜ[F] x i) = Φ x • a := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [extV, extF_tmul, LinearMap.comp_apply, ← Finset.sum_smul, ← map_sum]
  congr 2
  exact Finset.univ_sum_single x

theorem extV_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y y' : Fin n → AF F ⊗[F] E) : extV Φ (y + y') = extV Φ y + extV Φ y' := by
  simp [extV, map_add (f := _), Finset.sum_add_distrib]

theorem extV_neg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F)
    (y : Fin n → AF F ⊗[F] E) : extV Φ (-y) = -extV Φ y := by
  simp [extV, map_neg, Finset.sum_neg_distrib]

theorem extV_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (Φ : (Fin n → E) →ₗ[F] F) :
    extV Φ (0 : Fin n → AF F ⊗[F] E) = 0 := by
  simp [extV]

theorem smul_pairA {F : Type} [Field F] [NumberField F] (f : F) (α : Af F) :
    f • pairA F 0 α = pairA F 0 (f • α) :=
  Prod.ext (smul_zero f) rfl

theorem coord_int {D : D7} {S : HSp D} (L : Lat S) (Φ : (Fin S.rank → D.host.E) →ₗ[D.host.F] D.host.F)
    (hΦ : ∀ x ∈ L, Φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range) (z : Fin S.rank → D.host.E)
    (hz : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True)) :
    Φ z ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  have key : ∀ y ∈ latV S L (fun _ => True), ∃ β ∈ intAf D.host.F, extV Φ y = pairA D.host.F 0 β := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [one_mul]
      obtain ⟨c, hc⟩ := hΦ x hx
      refine ⟨algebraMap (𝓞 D.host.F) D.host.F c • α, smul_intAf c hαi, ?_⟩
      rw [extV_gen, ← hc, smul_pairA]
    | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [extV_zero]; rfl⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨β, hβ, e⟩ := hy
      obtain ⟨β', hβ', e'⟩ := hy'
      exact ⟨β + β', fun v => by rw [map_add]; exact add_mem (hβ v) (hβ' v),
        by rw [extV_add, e, e', GlobalTheory.FinPlLoc.pairA_add]⟩
    | neg y _ hy =>
      obtain ⟨β, hβ, e⟩ := hy
      exact ⟨-β, fun v => by rw [map_neg]; exact neg_mem (hβ v), by rw [extV_neg, e, GlobalTheory.FinPlLoc.pairA_neg]⟩
  obtain ⟨β, hβ, e⟩ := key _ hz
  rw [extV_gen, smul_pairA] at e
  have hb : Φ z • (1 : Af D.host.F) = β := congrArg Prod.snd e
  apply int_of_intAf
  rw [Algebra.algebraMap_eq_smul_one, hb]
  exact hβ

theorem mem_of_mem_latV : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsFullLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  intro D S L hL z hz
  classical
  let M : Submodule (𝓞 D.host.F) (Fin S.rank → D.host.E) := L.restrictScalars (𝓞 D.host.F)
  obtain ⟨t, g0, hg0, hgen⟩ := GlobalTheory.FinPlLoc.exists_gens L hL.fg
  have hMfg : M.FG := by
    refine ⟨Finset.univ.image g0, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hg0 k
    · intro x hx
      obtain ⟨c, rfl⟩ := hgen x hx
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul (𝓞 D.host.F)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F)))
      D.host.E := IsIntegralClosure.isLocalization (𝓞 D.host.F) D.host.F D.host.E (𝓞 D.host.E)
  have hden : ∀ v : Fin S.rank → D.host.E, ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ d • v ∈ M := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨⟨_, a, ha, rfl⟩, hs⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 D.host.E) (nonZeroDivisors (𝓞 D.host.F))) D.host.E _ v hv
    rw [Submodule.span_eq] at hs
    refine ⟨a, nonZeroDivisors.coe_ne_zero ⟨a, ha⟩, ?_⟩
    show a • v ∈ L
    rw [← IsScalarTower.algebraMap_smul (𝓞 D.host.E) a v]
    exact hs
  obtain ⟨m, g, Φ, hg, hΦ, hid⟩ := dual_gens (K := D.host.F) M hMfg hden
  rw [hid z]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := coord_int L (Φ k) (hΦ k) z hz
  rw [← hc, IsScalarTower.algebraMap_smul D.host.F c (g k)]
  exact (M.smul_mem c (hg k) : c • g k ∈ M)

end GlobalTheory.RatLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapRealTranslateEqRightTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothTranslate


open Classical in
theorem mult_equiv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => funext x; simp [rTr]
  | add T T' _ _ h h' =>
    funext x
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem translate : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  intro D V S θ M J χ T hT g
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V),
      T (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
        GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
        else v τ) x = T v (x * P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun v x => by simp⟩
    | insert a s ha ih =>
      obtain ⟨P, hP, hPe⟩ := ih
      refine ⟨atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) * P, mul_mem (Formalism.IndefR.TopMult.atTau_mem_GinfC θ a _) hP,
        fun v x => ?_⟩
      have hupd : (fun τ => if τ ∈ insert a s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) = Function.update (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) a ⟨M.rep a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) (v a),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ (v a).2⟩ := by
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd, mult_equiv θ M J χ T hT a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ _ (by simp [ha])]
      show T _ (x * atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a))) = _
      rw [hPe, mul_assoc]
  obtain ⟨P, hP, hPe⟩ := key Finset.univ
  exact ⟨P, hP, fun v x => by simpa using hPe v x⟩

end GlobalTheory.SmoothTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplits
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.FinPl.LatMem in
theorem GlobalTheory.FinPl.projB_mem_of_orthAt : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  intro D S A B o L LA LB hLG hO t ht
  apply hLG
  intro v
  have hY : (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈ latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h2 := ((hO v _).1 hY).2
  convert h2 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = (1 : AF D.host.F) ⊗ₜ[D.host.F] (o.qB i j) * _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

