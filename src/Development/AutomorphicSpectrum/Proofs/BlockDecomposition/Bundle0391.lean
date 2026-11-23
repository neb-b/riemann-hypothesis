module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import GroundTheory.AutomorphicForms.GLnLocal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfSmIndFixed
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped Topology

namespace GlobalTheory.CompanionTheory.LeviAdm

theorem finiteDimensional_of_smInd_fixed {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) (σ : Representation ℂ H W) (A : Submodule ℂ W)
    (hA : ∀ c : H, (c : G) ∈ K → ∀ w ∈ A, σ c w = w)
    (hfd : FiniteDimensional ℂ (fixed (smInd H σ) K)) : FiniteDimensional ℂ A := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → ∀ w ∈ A, σ q w = σ p w := by
    intro p q hpq w hw
    have h1 : σ (p⁻¹ * q) w = w := hA _ (by simpa using hpq) w hw
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q w = σ (p * (p⁻¹ * q)) w := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) w) := by rw [map_mul]; rfl
      _ = σ p w := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : A →ₗ[ℂ] (G → W) := LinearMap.pi fun x =>
    if S x then (σ (pick x)).comp A.subtype else 0
  have F_pos : ∀ (w : A) x, S x → F w x = σ (pick x) w := by
    intro w x h
    simp [F, h]
  have F_neg : ∀ (w : A) x, ¬ S x → F w x = 0 := by
    intro w x h
    simp [F, h]
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : ∀ w : A, F w ∈ indSpace H σ := by
    intro w q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos w _ hqx, F_pos w _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg w _ hqx, F_neg w _ hx, map_zero]
  have hfix : ∀ (w : A), ∀ c ∈ K, ∀ x, F w (x * c) = F w x := by
    intro w c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos w _ hxc, F_pos w _ hx]
      refine key _ _ ?_ w w.2
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg w _ hxc, F_neg w _ hx]
  have hfix' : ∀ (w : A), ∀ c ∈ K, ind H σ c ⟨F w, hlaw w⟩ = ⟨F w, hlaw w⟩ :=
    fun w c hc => Subtype.ext (funext fun x => hfix w c hc x)
  have hsm : ∀ w : A, (⟨F w, hlaw w⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun c hc => hfix' w c hc)
  have hT : ∀ w : A, (⟨⟨F w, hlaw w⟩, hsm w⟩ : smoothPart (ind H σ)) ∈ fixed (smInd H σ) K := by
    intro w c
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (hfix' w c c.2)
  let T : A →ₗ[ℂ] fixed (smInd H σ) K :=
    { toFun := fun w => ⟨⟨⟨F w, hlaw w⟩, hsm w⟩, hT w⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (Subtype.ext (map_add F a b)))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (Subtype.ext (map_smul F c a))) }
  have hS1 : S 1 := ⟨1, by simp [K.one_mem]⟩
  have hF1 : ∀ w : A, F w 1 = w := by
    intro w
    rw [F_pos w 1 hS1]
    refine (key 1 _ ?_ w w.2).trans (by simp)
    have h3 := K.inv_mem (pick_spec 1 hS1)
    simpa using h3
  have hinj : Function.Injective T := by
    intro a b hab
    have h4 : F a = F b := congrArg (fun t : fixed (smInd H σ) K => t.1.1.1) hab
    exact Subtype.ext (by rw [← hF1 a, ← hF1 b, h4])
  exact Module.Finite.of_injective T hinj

theorem isAdmissible_of_parInd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} (d : Fin s → ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth ρ → IsAdmissible (parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) ρ) → IsAdmissible ρ := by
  intro k _ _ _ _ s d W _ _ ρ hρ hA
  refine ⟨hρ, fun L hLo _ => ?_⟩
  let δ := deltaHalf k fun a => Fin (d a)
  let L' : Subgroup (Levi k fun a => Fin (d a)) := L ⊓ δ.ker
  have hL' : IsOpen (L' : Set (Levi k fun a => Fin (d a))) :=
    hLo.inter (isSmoothChar_deltaHalf k)
  have hpre := hL'.preimage (ProdIrr.continuous_leviProj (GlobalTheory.CompanionTheory.BZInd.stdE d))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have h1 : (1 : GL (Fin (∑ a, d a)) k) ∈ U := by
    have h2 : (1 : parab k (GlobalTheory.CompanionTheory.BZInd.stdE d)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simpa using L'.one_mem
    exact h2
  obtain ⟨m, -, hm⟩ :=
    (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (∑ a, d a)).mem_iff.1 (hU.mem_nhds h1)
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (∑ a, d a) m
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (∑ a, d a) m
  refine finiteDimensional_of_smInd_fixed (parab k (GlobalTheory.CompanionTheory.BZInd.stdE d))
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (∑ a, d a) m) hKo
    ((twist ρ δ).comp (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d))) (fixed ρ L) ?_ (hA.2 _ hKo hKc)
  intro c hc w hw
  have hcL : leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c ∈ L' := by
    have h2 : c ∈ Subtype.val ⁻¹' U := hm hc
    rw [hUe] at h2
    exact h2
  have hδ : δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) = 1 := MonoidHom.mem_ker.1 hcL.2
  have hw' := hw ⟨_, hcL.1⟩
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at hw'
  show ((δ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) : ℂˣ) : ℂ) •
    ρ (leviProj k (GlobalTheory.CompanionTheory.BZInd.stdE d) c) w = w
  rw [hδ, Units.val_one, one_smul]
  exact hw'

end GlobalTheory.CompanionTheory.LeviAdm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteInterCompact
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped Pointwise ENNReal
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ReproBessel

theorem finite_inter_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C) : ((Γ : Set G) ∩ C).Finite := by
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hK : IsCompact ((Γ : Set G) ∩ C) := hC.inter_left hcl
  have hΓ : DiscreteTopology (Γ : Set G) := inferInstanceAs (DiscreteTopology Γ)
  exact hK.finite ⟨DiscreteTopology.of_subset hΓ Set.inter_subset_left⟩

end GlobalTheory.CompanionTheory.ReproBessel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.BZMir

theorem continuous_gpProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  intro k _ _ _ _ m j
  have hincl : Continuous (GlobalTheory.BZMir.Leib.hgpIncl k m j) := by
    apply continuous_induced_rng.2
    have hv : Continuous (fun h : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j =>
        ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) := by
      first
        | exact continuous_subtype_val.comp continuous_subtype_val
        | fun_prop
    exact hv
  have hlevi := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ _ _
    (GlobalTheory.BZMir.Leib.eGP m j)).2.2.2.2.2.1
  have hblock := hlevi.comp hincl
  unfold GlobalTheory.BZMir.Leib.gpProj
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_apply false).comp hblock
  · apply continuous_induced_rng.2
    exact (continuous_apply true).comp hblock

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormula
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibGP

section SlopeTestRemainingChoices

variable (k : Type) [Field k]

theorem blockIndex_false (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨false, a⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin j) :
    eGP m j ⟨true, Fin.castSucc b⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨true, b⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem glEmbMat_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

end SlopeTestRemainingChoices

theorem gpProj_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  intro k _ _ _ _ m j p hp hp'
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  · apply Subtype.ext
    apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]

end GlobalTheory.CompanionTheory.LeibGP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.GpUnip

theorem mirUin_entry (k : Type) [Field k] (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n)
    (a b : Fin (n + 1)) (hb : b ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b := by
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hu)
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) a b = _
  simp [GlobalTheory.BZMir.colMat, hb]

theorem gpProj_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) →
      (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  intro k _ _ _ _ m j u hu
  have key : ∀ a b : Fin (m + j + 1), b ≠ Fin.last (m + j) →
      (((u : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b =
        (1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b :=
    fun a b hb => GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k (m + j) _ hu a b hb
  have e_inj := (GlobalTheory.BZMir.Leib.eGP m j).injective
  constructor
  · ext i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) false i i'
    refine h.trans ((key _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j i')).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Units.val_one]
  · have mem_of_proj (n : ℕ) (y : Mir k n) (hblock : ∀ i j : Fin n,
          ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
            (1 : Matrix (Fin n) (Fin n) k) i j) :
        y ∈ MirUin k n := by
      have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
          GlobalTheory.BZMir.eLast k n j :=
        fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
      rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
        MonoidHom.mem_range]
      refine ⟨Multiplicative.ofAdd fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
      apply Units.ext
      ext i j
      change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
      rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
          GlobalTheory.BZMir.eLast]
      · simp [hrow, GlobalTheory.BZMir.eLast]
    apply mem_of_proj j _
    intro i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) true (Fin.castSucc i) (Fin.castSucc i')
    have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i'⟩ ≠ Fin.last (m + j) :=
      fun hl => Fin.castSucc_ne_last i' ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).mp hl)
    refine h.trans ((key _ _ hne).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Fin.castSucc_inj, Units.val_one]

end GlobalTheory.CompanionTheory.GpUnip
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir.GpExists

section Entries

variable {k : Type} [Field k]

theorem unip_apply_of_ne_last (n : ℕ) (v : Multiplicative (Fin n → k)) (p q : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) p q = _
  simp [GlobalTheory.BZMir.colMat, hq]

theorem unip_apply_last_last (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) (Fin.last n) = 1
  simp [GlobalTheory.BZMir.colMat]

end Entries

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : (eGP m j ⟨false, a⟩ : Fin (m + j + 1)).val = a.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : (eGP m j ⟨true, b⟩ : Fin (m + j + 1)).val = m + b.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

end GlobalTheory.CompanionTheory.BZMir.GpExists

namespace GlobalTheory.CompanionTheory.BZMir

open GpExists

theorem exists_gpProj_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : Mir k j) (hu : u ∈ MirUin k j) :
    ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  have hu' : (u : GL (Fin (j + 1)) k) ∈ GlobalTheory.BZMir.MirU k j := by
    unfold GlobalTheory.BZMir.MirUin at hu
    exact Subgroup.mem_subgroupOf.1 hu
  unfold GlobalTheory.BZMir.MirU at hu'
  rw [MonoidHom.mem_range] at hu'
  obtain ⟨w, hw⟩ := hu'
  set v' : Multiplicative (Fin (m + j) → k) :=
    Multiplicative.ofAdd (Fin.append (0 : Fin m → k) (Multiplicative.toAdd w)) with hv'
  have hU : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.MirU k (m + j) := by
    unfold GlobalTheory.BZMir.MirU
    exact MonoidHom.mem_range.2 ⟨v', rfl⟩
  have hM : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.Mir k (m + j) :=
    GlobalTheory.BZMir.MirU_le_Mir k (m + j) hU
  have hP : (⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩ : GlobalTheory.BZMir.Mir k (m + j)) ∈
      GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
    unfold GlobalTheory.BZMir.Leib.MirabolicParabolic
    rw [Subgroup.mem_comap]
    show GlobalTheory.BZMir.unip k (m + j) v' ∈ _
    refine (GlobalTheory.SmGL.mem_parab_two k).2 (fun b a => ?_)
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last]
    · exact Matrix.one_apply_ne (fun h => by simpa using Equiv.injective _ h)
    · exact GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a
  refine ⟨⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩, ?_, ?_⟩
  · unfold GlobalTheory.BZMir.MirUin
    exact Subgroup.mem_subgroupOf.2 hU
  apply Prod.ext
  · apply Units.ext
    ext a a'
    simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply]
    rw [GlobalTheory.SmGL.leviProj_apply]
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a')]
    by_cases h : a = a'
    · subst h
      simp
    · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
        Units.val_one, Matrix.one_apply_ne h]
  · apply Subtype.ext
    apply Units.ext
    ext b b'
    first
    | (show ((GlobalTheory.SmGL.leviProj k (GlobalTheory.BZMir.Leib.eGP m j)
          (GlobalTheory.BZMir.Leib.hgpIncl k m j ⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩) true :
          GL _ k) : Matrix _ _ k) b b' = _
       rw [GlobalTheory.SmGL.leviProj_apply])
    | (simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.codRestrict_apply,
          MonoidHom.coe_codRestrict, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_mk]
       rw [GlobalTheory.SmGL.leviProj_apply])
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [← hw]
    induction b' using Fin.lastCases with
    | last =>
      rw [GlobalTheory.BZMir.Leib.blockIndex_true_last]
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.BZMir.Leib.blockIndex_true_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last,
          GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last]
      | cast i =>
        have hidx : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ = Fin.castSucc (Fin.natAdd m i) :=
          Fin.ext (by simp [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val])
        rw [hidx, GlobalTheory.BZMir.unip_apply_castSucc_last, GlobalTheory.BZMir.unip_apply_castSucc_last, hv']
        simp
    | cast i =>
      have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ ≠ Fin.last (m + j) :=
        fun h => Fin.castSucc_ne_last i ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).1 h)
      rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ hne,
        GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last i)]
      by_cases h : b = Fin.castSucc i
      · subst h
        simp
      · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
          Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.BZMir

end
end

