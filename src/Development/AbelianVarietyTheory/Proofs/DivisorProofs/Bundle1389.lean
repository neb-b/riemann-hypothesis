module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open Matrix

noncomputable section

namespace GlobalTheory.FlagRad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem mulVec_initCols_mem {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (m : Fin r) (A : Set (Fin r))
    (a : Fin (m.val + 1) → AF F ⊗[F] E) (ha : ∀ l, a l ≠ 0 → Fin.castLE m.2 l ∈ A) :
    adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a ∈ GlobalTheory.StdPar.colSpan F X A := by
  rw [Matrix.mulVec_eq_sum]
  refine sum_mem fun l _ => ?_
  by_cases h : a l = 0
  · simp [h]
  · rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ha l h, rfl⟩)

theorem exists_of_card_lt {r : ℕ} (S : Finset (Fin r)) {a b : ℕ}
    (h : (S.filter fun k => k.val < a).card < (S.filter fun k => k.val < b).card) :
    ∃ k ∈ S, a ≤ k.val ∧ k.val < b := by
  by_contra hc
  push_neg at hc
  refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_le.1 fun h' => absurd hk.2 (not_lt.2 (hc k hk.1 h'))⟩


open GlobalTheory.StdPar in
theorem unipFlag_le_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (m : Fin r) (hmS : m ∈ S)
    (hm : ∀ k ∈ S, k ≤ m) :
    GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤
      GlobalTheory.StdPar.unip σ J X S := by
  set C := initCols X m with hCdef
  set d : Fin (m.val + 1) → ℕ := fun i => (S.filter fun k => k.val < i.val).card with hd
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hC : IsIsoCols σ J C := isIsoCols_of_isWittFrame hW hσ hJ m.2
  have memS : ∀ g ∈ unipFlag σ J C d, g ∈ unipSet σ J C d := fun g hg => (mem_unipFlag hJ hσ hC d).1 hg

  have stab : ∀ g ∈ unipSet σ J C d, ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y ∈ colSpan F X A, (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := by
    intro g hg A hA1 hA2 y hy
    have hle : colSpan F X A ≤ (colSpan F X A).comap (matHom _ σ J g).1.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨a, ha0, ha⟩ := hg.1 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩
      have ha' : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
      have e : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i + ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      show (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ colSpan F X A
      rw [e, ha']
      refine add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (GlobalTheory.FlagRad.mulVec_initCols_mem X m A a fun l' hl' => ?_)
      exact hA2 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩ l' hi (not_le.1 fun h' => hl' (ha0 l' h'))
    exact hle hy
  have inv_app : ∀ (g : GAd σ J) y, (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := fun g y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  intro g hg
  have hg1 := memS g hg
  have hg2 := memS g⁻¹ (inv_mem hg)
  have iffPart : ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y, y ∈ colSpan F X A ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := fun A hA1 hA2 y =>
    ⟨stab g hg1 A hA1 hA2 y, fun hy => by
      have := stab g⁻¹ hg2 A hA1 hA2 _ hy
      rwa [inv_app] at this⟩
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (hm k hk), fun hi => ⟨m, hmS, hi⟩⟩
  have hB1 : ∀ i ∈ {i : Fin r | i ≤ m}, i.val ≤ m.val := fun i hi => hi
  have hB2 : ∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ {i : Fin r | i ≤ m} → d l' < d l →
      Fin.castLE m.2 l' ∈ {i : Fin r | i ≤ m} := fun l l' _ _ => Nat.le_of_lt_succ l'.2
  have sub_app : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1) *ᵥ y := fun y => by
    simp [Matrix.sub_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨iffPart _ ?_ ?_, fun y hy => ?_⟩, ?_⟩
  · rintro i ⟨k, hk, hik, -⟩
    exact hik.trans (hm k hk)
  · rintro l l' ⟨k, hk, hlk, hkj⟩ hdl
    obtain ⟨k', hk', h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S hdl
    refine ⟨k', hk', h1, ?_⟩
    rw [Fin.le_def] at hlk
    rw [Fin.lt_def] at hkj ⊢
    simp only [Fin.coe_castLE] at hlk
    omega
  ·
    have hle : colSpan F X {j} ≤ (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi', rfl⟩
      have hij : i = j := hi'
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      by_cases hi : i.val ≤ m.val
      · obtain ⟨a, ha0, ha⟩ := hg1.1 ⟨i.val, Nat.lt_succ_of_le hi⟩
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' hl' => ?_
        obtain ⟨k, hk, h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S (not_le.1 fun h' => hl' (ha0 l' h'))
        refine ⟨k, hk, h1, ?_⟩
        rw [Fin.lt_def, ← hij]
        exact h2
      · have hx : (cT (σ : E →+* E) C * J) *ᵥ (fun k => X k i) = 0 :=
          funext fun l => congrFun (congrFun hW.xx (l.castLE m.2)) i
        obtain ⟨a, ha⟩ := hg1.2 _ hx
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' _ => ⟨m, hmS, Nat.le_of_lt_succ l'.2, ?_⟩
        rw [Fin.lt_def, ← hij]
        omega
    rw [sub_app]
    exact hle hy
  · rw [e1]
    refine ⟨iffPart _ hB1 hB2, fun y hy => ?_⟩
    set T := cT (σ : E →+* E) (initCols X m) * J
    have hT : T * initCols Y m = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hW.xy (i.castLE m.2)) (j.castLE m.2)).trans (by simp [Matrix.one_apply])
    have hQ : T * (1 - initCols Y m * T) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
    have hy' : y = adMat F (1 - initCols Y m * T) *ᵥ y := by
      rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
        one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
    have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, hy', mulVec_eq_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [op_smul_eq_smul, map_smul]
    obtain ⟨a, ha⟩ := hg1.2 (fun i => (1 - initCols Y m * T : Matrix (Fin n) (Fin n) E) i j)
      (funext fun i => congrFun (congrFun hQ i) j)
    exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)

end GlobalTheory.FlagRad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimes
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FreeLev

@[instance_reducible] def ptModule {E : Type} [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) :
    letI := P.isAb.comm
    Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) :=
  letI := P.isAb.comm
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  { smul := fun c q => Additive.ofMul (q.toMul ≫ act.act c)
    one_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 1) = q
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a * b)) = Additive.ofMul ((q.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm, act.mul, Category.assoc]
    smul_zero := fun c => by
      haveI := act.hom c
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ act.act c) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun c q q' => by
      haveI := act.hom c
      show Additive.ofMul ((q.toMul * q'.toMul) ≫ act.act c) = Additive.ofMul (q.toMul ≫ act.act c * q'.toMul ≫ act.act c)
      rw [MonObj.mul_comp]
    add_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a + b)) = Additive.ofMul (q.toMul ≫ act.act a * q.toMul ≫ act.act b)
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [h0, MonObj.comp_one] }


set_option maxHeartbeats 800000 in
theorem free_of_unip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  intro E _ _ _ H Dw l Xo c G _ h m g₁ g₂ I₁ I₂ _ hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ hu₁ hu₂ hfaith
  intro g k _ _ y y' hR hx
  obtain ⟨ρ, ν, -, hlev, hmove⟩ := hR
  have hfix : y.x ≫ ρ = y.x := hmove.1.symm.trans hx
  obtain ⟨x', hx'⟩ := _root_.GlobalTheory.FixedCx.exists_fixed_complex_point E H Dw l Xo k y.x ρ hfix
  obtain ⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩ :=
    _root_.GlobalTheory.LevMoveFibre.exists_fibreAut E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'
  have hM0 : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩ :=
    _root_.GlobalTheory.periodLattice_of_finiteOrder E P act θ N l.M hθ hN hθN hcomm hM0
  letI := P.isAb.comm
  letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := ptModule P act
  let evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_add' := fun a b => congrArg Additive.ofMul (hadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }
  let ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ψ a)
      map_add' := fun a b => congrArg Additive.ofMul (hψadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }
  let θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun q => Additive.ofMul (q.toMul ≫ θ)
      map_add' := fun q q' => by
        show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)
        rw [MonObj.mul_comp]
      map_smul' := fun c q => by
        show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)
        rw [Category.assoc, Category.assoc, hcomm] }
  have hMmem : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact Ideal.mul_le_left h1
  refine hfaith g (_root_.GlobalTheory.sub_mem_smul_top_of_neat_level E Dw.La Λ _ l.Mb l.M N m g₁ g₂ I₁ I₂ evL ψL θL F (h g) hfin htf hM0 hMmem
    (fun a => by
      show Additive.ofMul (ev a) = 0 ↔ _
      rw [← hker a]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨a, ha⟩ := honto q.toMul (fun c hc => by
        have := hq c hc
        exact congrArg Additive.toMul this)
      exact ⟨a, congrArg Additive.ofMul ha⟩)
    (fun b => by
      show Additive.ofMul (ψ b) = 0 ↔ _
      rw [← hψker b]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨b, hb⟩ := hψonto q.toMul (by
        have := congrArg Additive.toMul hq
        rwa [toMul_nsmul] at this)
      exact ⟨b, congrArg Additive.ofMul hb⟩)
    (fun b => congrArg Additive.ofMul (hψF b))
    (fun a => congrArg Additive.ofMul (hrel a))
    hN hFN hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ (hu₁ g) (hu₂ g))

end GlobalTheory.FreeLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfHyps
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.GKNorm.exists_twist_isNormalised E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]


end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _



end GlobalTheory.GLTwoHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.RankBound

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y ≤ D := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  replace hU : IsAffineOpen (X := Y) U := hU
  refine ⟨U, U.isOpen, hx, le_of_eq ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
    (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)

theorem rankLow : Quoted → RankLow := by
  intro Q F _ _ G hnef hbig T
  have hV := G.geom.alg.variety
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · rw [Nat.zero_sub, Nat.choose_eq_zero_of_lt hV.one_le, Nat.cast_zero, zero_mul]
    exact Int.natCast_nonneg _
  have hstr : strHom F G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F (X := G.Y)) := hstr ▸ hV.proj
  have hdim := topologicalKrullDim_le_of_smooth G.str G.D hV.smooth
  have hM : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  let e : twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA) ≅ LB.toMod (tens G.K.bundle G.LA) :=
    Twist.unitTwistIso _
  have hq := Twist.isFiniteQC_twist (F := GlobalTheory.structureModule G.Y) hM
  have hvan : VanishFrom G.L (twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA)) 1 := fun j hj q hq =>
    (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q ((twistFunctor (lbZPow G.L j)).mapIso e)).toEquiv.subsingleton_congr.2
      (_root_.GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj Q F G hnef hbig j (by omega) q hq)
  have key := GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim F G.Y hproj G.L G.isLB G.N G.b
    (fun y => TopologicalSpace.Opens.mem_iSup.1 (G.geom.alg.bpf.ge (Set.mem_univ y))) G.D _
    ((suppDim_le _).trans hdim) 1 hvan (T - 1)
  rw [(diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom F G.Y) (GlobalTheory.structureModule G.Y) hproj
    ((suppDim_le _).trans hdim)).interNum_twist (by simp) (fun _ => G.isLB) hM] at key
  have hT' : (1 : ℤ) + ((T - 1 : ℕ) : ℤ) = T := by omega
  rw [hT'] at key
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule G.Y) hM (Twist.isLB_lbZPow G.isLB T)
    (G.isLB_adj T) rfl
  rw [G.finrank_global, lbH0, ← hdim_congr F 0 i]
  exact key

end GlobalTheory.HSCore.RankBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedQuotientMapFiniteFlatSurjective
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuotGlue

theorem of_local (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (hψ : ∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j))
    (hc : ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left)
    (hq : ∀ j, P (q j).left) : P Q.left := by
  have sq : ∀ j, IsPullback (pullback.fst A.hom (𝒰.f j)) (q j).left Q.left (ψ j) := fun j => by
    refine IsPullback.of_bot ?_ (hc j).symm (hψ j)
    have e1 : (q j).left ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := Over.w (q j)
    have e2 : Q.left ≫ G.hom = A.hom := Over.w Q
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have hoi : ∀ j, IsOpenImmersion (ψ j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hψ j).flip inferInstance
  have cov : ∀ x : G.left, ∃ j y, ψ j y = x := by
    intro x
    obtain ⟨j, u, hu⟩ := 𝒰.exists_eq (G.hom x)
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback (hψ j) x u hu.symm
    exact ⟨j, p, hp⟩
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers 𝒰.I₀ (fun j => (B j).left) ψ cov) fun j => ?_
  have h := hq j
  rw [← (sq j).isoPullback_hom_snd, P.cancel_left_of_respectsIso] at h
  exact h

theorem finite_flat_surjective : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) →
    (∀ j, IsFinite (q j).left) → (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) →
    IsFinite Q.left ∧ Flat Q.left ∧ Surjective Q.left := by
  intro S 𝒰 A G Q B ψ q hψ hc hf hfl hs
  have : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_local @IsFinite S 𝒰 A G Q B ψ q hψ hc hf, of_local @Flat S 𝒰 A G Q B ψ q hψ hc hfl,
    of_local @Surjective S 𝒰 A G Q B ψ q hψ hc hs⟩

end GlobalTheory.QuotGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRightMulActionLaws
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.FinEtRank.isIsogDeg_of_card :
  ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  intro S A K i hi hfin het d hd hcard
  have h : (toUnit K).left = K.hom := by simpa using Over.w (toUnit K)
  have hrank : ∀ s : S, K.hom.finrank s = d := by
    intro s
    obtain ⟨k, _, _, t, ht⟩ := GlobalTheory.FinEt.exists_algClosed_point S s
    obtain ⟨z, rfl⟩ : s ∈ Set.range t := by rw [ht]; rfl
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank K.hom t z
    rw [← hc, ← hcard k t]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨Over.homMk x.1 x.2 ≫ i, ⟨Over.homMk x.1 x.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have := (cancel_mono i).1 (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg CommaMorphism.left this)
    · rintro ⟨y, y', hy'⟩
      refine ⟨⟨y'.left, Over.w y'⟩, Subtype.ext ?_⟩
      simp only
      rw [← hy']
      congr 1
  have hflat : Flat K.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact hfin
  · rw [h]; exact hflat
  · rw [h]; exact (Scheme.Hom.one_le_finrank_iff_surjective K.hom).1 fun s => (hrank s).symm ▸ hd
  · intro y; rw [h]; exact hrank y
end

