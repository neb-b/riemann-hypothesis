module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidal
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericConstituent

variable {g : ℕ} [Fact g.Prime]

theorem wh_const_mul' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_mul_const' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_list_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (L : List (Gn g n → ℂ)) :
    wh ψ L.sum = (L.map (wh ψ)).sum := by
  induction L with
  | nil => simp [wh, tr]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold wh tr
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_list_sum_right {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (L : List (G → ℂ)) :
    ip ρ L.sum = (L.map (ip ρ)).sum := by
  induction L with
  | nil => simp [ip]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_sum_count {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (hρ : IsIrr ρ) (L : List (G → ℂ))
    (hL : ∀ σ ∈ L, IsIrr σ) : (L.map (ip ρ)).sum = (L.count ρ : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun σ hσ => hL σ (List.mem_cons_of_mem a hσ)), List.count_cons,
      (GlobalTheory.GLq.ZOrth.zorth G ρ a hρ (hL a List.mem_cons_self)).2.2]
    by_cases h : ρ = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem isClass_of_isChar {n : ℕ} {χ : Gn g n → ℂ} (h : IsChar χ) : IsClass χ :=
  (GlobalTheory.charDec (Gn g n) χ).2.2.1 h

theorem wh_hcL_prod (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) → wh ψ (hcL L (degL L)) = (L.map fun p => wh ψ p.2).prod := by
  intro L
  induction L with
  | nil =>
    intro _
    exact GlobalTheory.GLq.Leibniz.wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl
        (fun q hq => isChar_of_isIrr (hL' q hq).2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul']
      rw [wh_mul_const', ih hL', List.map_cons, List.prod_cons]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem exists_generic_constituent : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) →
      ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  intro g _ ψ hψ L n hn hL
  subst hn
  have hwh : wh ψ (hcL L (degL L)) ≠ 0 := by
    rw [wh_hcL_prod ψ hψ L hL]
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    obtain ⟨m, hm, hm'⟩ := _root_.GlobalTheory.GLq.wh_cusp_pos g ψ hψ p.1 p.2 (hL p hp)
    rw [hm'] at h1
    have : m = 0 := by exact_mod_cast h1
    omega
  have hch : IsChar (hcL L (degL L)) :=
    (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL q hq).2.1)).1
  obtain ⟨Lρ, hirr, hsum⟩ := (GlobalTheory.charDec _ (hcL L (degL L))).1 hch
  have hex : ∃ ρ ∈ Lρ, wh ψ ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hwh
    rw [hsum, wh_list_sum]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      exact hno ρ hρ
  obtain ⟨ρ, hρ, hwρ⟩ := hex
  refine ⟨ρ, hirr ρ hρ, hwρ, ?_⟩
  rw [hsum, ip_list_sum_right, ip_sum_count ρ (hirr ρ hρ) Lρ hirr]
  exact Nat.cast_ne_zero.2 (List.count_pos_iff.2 hρ).ne'

end GlobalTheory.GLq.GenericConstituent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryFrobeniusFixed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PhiFix

theorem frob_actB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (x : TW (OB l O) T) :
    TWmap (frobOB l O) T (actB (sQ l) T g x) = actB (sQ l) T g (TWmap (frobOB l O) T x) := by
  have hB : ∀ r : OB l O, frobOB l O (galOB O (sQ l g) r) = galOB O (sQ l g) (frobOB l O r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul o β =>
      simp only [frobOB, galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1 _ β)
    | add r s hr hs => rw [map_add (galOB O (sQ l g)), map_add (frobOB l O), map_add (frobOB l O), map_add (galOB O (sQ l g)), hr, hs]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [actB, TWmap, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem frob_fixed_coboundary : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hb g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hb₀, rfl⟩ := hb
  haveI : CompleteSpace K := _root_.GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall l O K
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi O K l e a ι η H D y hyY σ.1 hconn
  obtain ⟨-, hall⟩ := _root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι D.toPhiMod T R.I
  obtain ⟨hφ, huniq, hfrobv, -, -⟩ := hall R.jB R.cmp
  have hσφ : D.phi σ.1 ∈ D.MMl := _root_.GlobalTheory.BK.BKDat.phi_mem_MMl O K l e a ι η H D σ.1 σ.2
  have hyφ : D.phi y ∈ D.MMl := _root_.GlobalTheory.BK.phi_mem_MMl_of_mem_Y O K l e a ι η H D y hyY

  have hv1 := IsCrisVal.sub t ϖ (hfrobv _ _ hb₀) hb₀
  have hv2 := _root_.GlobalTheory.BKGal.PhiVal.isCrisVal_phi l a e O K t ϖ ι η H D T R.jB y hyY hy hyφ
  have hw : phiW t ϖ D.toPhiMod (phiW t ϖ D.toPhiMod m₀) - phiW t ϖ D.toPhiMod m₀ =
      phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩) := by rw [← hm₀, map_sub]
  rw [hw] at hv1
  have hb0 := huniq _ _ _ hv1 hv2
  have hs := hφ σ ⟨D.phi σ.1, hσφ⟩ rfl
  have hmem : D.xi d ∈ D.MMl := by
    rw [← hd]; exact sub_mem (sub_mem hσφ σ.2) hyφ
  have hkey : TWmap (frobOB l O) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) -
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) = R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi d, hmem⟩) := by
    have he : (⟨D.xi d, hmem⟩ : D.MMl) = ⟨D.phi σ.1, hσφ⟩ - σ - ⟨D.phi y, hyφ⟩ := Subtype.ext (by
      simp only [Submodule.coe_sub]; exact hd.symm)
    rw [he, map_sub, map_sub, map_sub, map_sub, map_sub, ← hs, ← hb0]
    abel
  have hfix := R.horiz g hg d hmem
  rw [← hkey, map_sub] at hfix
  rw [map_sub, frob_actB]
  exact sub_eq_sub_iff_sub_eq_sub.1 hfix

end GlobalTheory.BKGal.PhiFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizXi

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι]


omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in
theorem desc_succ_eq_zero {P : PhiMod O K l e a ι} (D : Conn P) {v : Vec K a ι} (hv : D.N v = 0) (i : ℕ) :
    D.desc (i + 1) v = 0 := by
  induction i with
  | zero => simp [Conn.desc_succ, Conn.desc_zero, hv]
  | succ i ih => rw [Conn.desc_succ, hv, zero_sub, map_neg, map_nsmul, ih, smul_zero, neg_zero]

theorem muDiv_zero (g : ↥(GK (ϖ.field a))) : ϖ.muDiv a O g 0 = 1 := by
  simp only [PiSys.muDiv, dpow_zero]
  rfl

theorem taylor_fix (g : ↥(GK (ϖ.field a))) {P : PhiMod O K l e a ι} (D : Conn P) (Γ : Matrix ι ι (OA l O))
    (m : P.MM) (hm : D.N m.1 = 0)
    (h : ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ z : ι → OCr l O,
      (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) -
        ∑ i ∈ Finset.range n, ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ =
          (l : OCr l O) ^ r • z) :
    (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) = toCris t ϖ P m := by
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1),
      ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ = toCris t ϖ P m := by
    intro n
    rw [Finset.sum_range_succ']
    have h0 : ∀ i ∈ Finset.range n, ϖ.muDiv a O g (i + 1) •
        toCris t ϖ P ⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ = 0 := by
      intro i _
      have : (⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ : P.MM) = 0 :=
        Subtype.ext (desc_succ_eq_zero D hm i)
      rw [this, map_zero, smul_zero]
    rw [Finset.sum_eq_zero h0, zero_add, muDiv_zero, one_smul]
    exact congrArg _ (Subtype.ext (D.desc_zero m))
  funext i
  rw [← sub_eq_zero]
  refine sep_OCr _ fun r => ?_
  obtain ⟨n₀, hn₀⟩ := h r
  obtain ⟨z, hz⟩ := hn₀ (n₀ + 1) (Nat.le_succ _)
  rw [hsum] at hz
  exact ⟨z i, by rw [← Pi.sub_apply, hz, Pi.smul_apply, smul_eq_mul]⟩

theorem toBcris_eq_toOB {P : PhiMod O K l e a ι} (m : P.MMl) (hm : m.1 ∈ P.MM) (i : ι) :
    toBcris t ϖ P m i = toOB l O (toCris t ϖ P ⟨m.1, hm⟩ i) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem exists_pow_smul_mem_MM {P : PhiMod O K l e a ι} (m : P.MMl) :
    ∃ N : ℕ, (((l ^ N : ℕ) • m : P.MMl) : Vec K a ι) ∈ P.MM := by
  have hc : ∀ τ i, ∃ n : ℕ, ((l : S O K e) : K⟦X⟧) ^ n * (P.mxInv τ *ᵥ m.1 τ) i ∈ S O K e :=
    fun τ i => mem_away.1 (P.mem_extc_iff.1 (mem_tot.1 m.2 τ) i)
  choose n hn using hc
  refine ⟨∑ τ, ∑ i, n τ i, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_⟩
  have hle : n τ i ≤ ∑ τ, ∑ i, n τ i :=
    (Finset.single_le_sum (f := fun i => n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  have h1 : ((((l ^ (∑ τ, ∑ i, n τ i) : ℕ) • m : P.MMl) : Vec K a ι)) τ =
      ((l : S O K e) : K⟦X⟧) ^ (∑ τ, ∑ i, n τ i) • m.1 τ := by
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul K⟦X⟧]
    simp
  rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (S O K e).mul_mem ((S O K e).pow_mem (SetLike.coe_mem _) _) (hn τ i)

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : OB l O) (z : TW (OB l O) T) : actB s T g (r • z) = galOB O (s g) r • actB s T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [actB, TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable [TameDescentExponentData K l e a]

theorem actB_jB {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (y : ι → OB l O) :
    actB (sQ l) T g (jB y) = jB (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (y i)) := by
  obtain ⟨-, hI⟩ := _root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι P T I
  obtain ⟨-, huniq, -, -, hgal⟩ := hI jB hjB
  have hstab := (I.exists_isLMat_iff (sQ l g) g).1 ⟨Γ, hΓ⟩
  have hval : ∀ c : ι → OA l O, IsCrisVal t ϖ P jB (inclL t ϖ P c) (jB fun i => toB l O (c i)) :=
    fun c => ⟨1, c, by simp, by simp, by simp⟩
  have hbas : ∀ j, actB (sQ l) T g (jB (Pi.single j 1)) = jB (Γ.map (toB l O) *ᵥ Pi.single j 1) := by
    intro j
    have e1 : (Pi.single j 1 : ι → OB l O) = fun i => toB l O ((Pi.single j 1 : ι → OA l O) i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have e2 : (Γ.map (toB l O) *ᵥ Pi.single j 1) = fun i => toB l O
        ((Γ *ᵥ fun k => galOA O (sQ l g) ((Pi.single j 1 : ι → OA l O) k)) i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite (galOA O (sQ l g)), apply_ite (toB l O)]
    have h1 := hgal g hstab _ _ (hval (Pi.single j 1))
    rw [hΓ] at h1
    rw [e2, e1]
    exact huniq _ _ _ h1 (hval _)
  conv_lhs => rw [pi_eq_sum_univ' y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' (fun i => galOB O (sQ l g) (y i))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.mulVecLin_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearEquiv.map_smul, actB_smul, hbas, map_smul, Matrix.mulVecLin_apply, LinearEquiv.map_smul]

theorem horiz_of_fix {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (ξ : P.MMl) (N : ℕ)
    (hN : (((l ^ N : ℕ) • ξ : P.MMl) : Vec K a ι) ∈ P.MM)
    (hfix : (Γ.map (toOCr l O) *ᵥ fun i => galOCr O (sQ l g) (toCris t ϖ P ⟨_, hN⟩ i)) =
      toCris t ϖ P ⟨_, hN⟩) :
    actB (sQ l) T g (jB (toBcris t ϖ P ξ)) = jB (toBcris t ϖ P ξ) := by
  have hB : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ((l ^ N : ℕ) • ξ) i)) =
      toBcris t ϖ P ((l ^ N : ℕ) • ξ) := by
    funext i
    rw [toBcris_eq_toOB t ϖ _ hN i, ← hfix]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toBcris_eq_toOB t ϖ _ hN, galOB_toOB,
      Matrix.map_apply, toB, AlgHom.comp_apply]
  rw [map_nsmul] at hB
  have hu : IsUnit ((l ^ N : ℕ) : OB l O) := by
    rw [Nat.cast_pow]; exact isUnit_l_OB.pow N
  have hg : (fun i => galOB O (sQ l g) (((l ^ N : ℕ) • toBcris t ϖ P ξ) i)) =
      (l ^ N : ℕ) • fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [hg, Matrix.mulVec_smul] at hB
  have hfx : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i)) = toBcris t ϖ P ξ := by
    funext i
    have h3 := congrFun hB i
    simp only [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (OB l O), smul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  rw [actB_jB t ϖ I jB hjB g Γ hΓ _, hfx]

end General

end GlobalTheory.HorizXi

namespace GlobalTheory.HorizXi

theorem galois_fixes_xi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB hjB C hC hTay g hg d hξ
  have h1 := hTay ⟨sQ l g, hg⟩
  obtain ⟨Γ, h2⟩ := h1
  have h3 := exists_pow_smul_mem_MM (⟨P.xi d, hξ⟩ : P.MMl)
  obtain ⟨N, hN⟩ := h3
  have hNm : C.N (((l ^ N : ℕ) • (⟨P.xi d, hξ⟩ : P.MMl) : P.MMl) : Vec _ a ι) = 0 := by
    rw [Submodule.coe_smul_of_tower, map_nsmul, Conn.N_apply, hC, PhiMod.nabla_xi, smul_zero, smul_zero]
  exact horiz_of_fix (thetaW a LL) ϖ I jB hjB g Γ h2.1 _ N hN
    (taylor_fix (thetaW a LL) ϖ ⟨sQ l g, hg⟩ C Γ ⟨_, hN⟩ hNm (h2.2 ⟨_, hN⟩))

end GlobalTheory.HorizXi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree
section
noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRham
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isDR_of_frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hF
  obtain ⟨Y, Y', hY, -⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨B, Q, -, hQ, -, -, hinv⟩ := _root_.GlobalTheory.BKLim.InvBasis.exists_invariant_basis l K bk τ hτ C N d (fun g => (ρ g).val) F Y hF hY
  have hQ' : IsUnit (T.eD.symm.mapMatrix Q) := hQ.map T.eD.symm.mapMatrix
  refine GlobalTheory.PMon.isDR_of_periodMatrix l P (Fin d) K (Fin d → ℚ_[l]) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hQ'.unit ?_
  intro g
  have hg := hinv g
  simp only [IsUnit.unit_spec]
  ext i j
  apply T.eD.injective
  have hij := congrFun (congrFun hg i) j
  rw [LinearMap.toMatrix_eq_toMatrix']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qRep, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.mapMatrix_apply] at hij ⊢
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Units.coeHom_apply, RingHom.mapMatrix_apply, AlgEquiv.coe_toAlgHom, Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_toLin',
    Matrix.map_apply, T.actD, RingEquiv.apply_symm_apply] at ⊢
  rw [← hij]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have e : LinearMap.toMatrix' (Matrix.toLinAlgEquiv' ((algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]))) =
      (algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) :=
    LinearMap.toMatrix'_toLin' _
  erw [e]
  exact T.zD ((ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) i x)

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  first | exact @GlobalTheory.BKExact.isExactTriple_of_isSESLat | exact GlobalTheory.BKExact.isExactTriple_of_isSESLat | (intros; apply GlobalTheory.BKExact.isExactTriple_of_isSESLat <;> assumption)
end

