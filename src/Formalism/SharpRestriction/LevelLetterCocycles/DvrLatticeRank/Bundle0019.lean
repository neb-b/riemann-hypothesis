module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAB
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_αβ_core (Bs : FramepfBas W T) (hT : IsCrys PD T.ρ) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ)
    (eb : Fin Bs.r → LcQ W T π' c) (P R S : Fin Bs.r → Fin Bs.r → LetA O n) (hS : ∀ m k, S m k ∈ W.AΔ)
    (lam : O) (hRP : ∀ m k, ∑ j, R m j * P j k =
      (if m = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S m k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) : Ψ (Φ y) - lam • y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨h1, hΔ, hl⟩ := (mem_LamPS W T Eπ h' c y).1 hy
  obtain ⟨a, haΔ, hac, ha⟩ := framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1)
    (fun δ hδ => by rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ])
    (by rw [smul_comm, hl])
  refine ⟨∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m), framepf_mem_Pc Bs c _
    (fun m => Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS m k)) (fun m => ?_), ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hac]
  show (π' ^ M * Eπ ^ (3 * h')) • (∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m)) = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  have h2 : Eπ ^ h' • Ψ (Φ y) = ∑ m, (∑ j, (∑ k, a k * P j k) * R m j) • W.φD T (Bs.b m) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← algebraMap_smul W.EE, ← map_smul, ← map_smul, algebraMap_smul, ha, hΦ, map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ m, ∑ j, (∑ k, a k * P j k) * R m j =
      algebraMap O (LetA O n) lam * a m + π' ^ M * Eπ ^ (4 * h') * ∑ k, a k * S m k := by
    intro m
    have : ∑ j, (∑ k, a k * P j k) * R m j = ∑ k, a k * ∑ j, R m j * P j k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hRP, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · rw [mul_left_comm, mul_comm (a m), hac]
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : Eπ ^ h' • (lam • y) = ∑ m, (algebraMap O (LetA O n) lam * a m) • W.φD T (Bs.b m) := by
    rw [smul_comm, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_smul, algebraMap_smul]
  rw [smul_sub, smul_sub, h2, h4, smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [h3, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul (LetA O n) (W.φD T (Bs.b m)) using 2
  ring

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAsm
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n)

structure FramepfData (T : LocLat G Qp LL O) (hh : LcQ W T π' c →ₗ[O] W.DD T)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c) : Prop where
  hγ : ∀ ℓ, W.γD T W.gam (hh ℓ) - hh ℓ ∈ PiNS W T π' M
  hmod : ∀ z hz, hh (mkL W T π' c z hz) - ((PD.p : ℕ) : O) ^ σ • z ∈ PiNS W T π' 1
  hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ)
  ΨJ : ∀ x ∈ JLA W T π' Eπ h' M c, Ψ x ∈ JP W T π' Eπ h' M c
  ΦJ : ∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c
  βα : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, Φ (Ψ x) - ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c
  αβ : ∀ y ∈ LamPS W T Eπ h' c, Ψ (Φ y) - ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ JP W T π' Eπ h' M c
  sat : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c →
    x ∈ JLA W T π' Eπ h' M c
  inj : ∀ x ∈ PiNS W T π' 1, W.γD T W.gam x - x ∈ PiNS W T π' M → x ∈ PiNS W T π' M
  loc : ∀ τ ζ, Pt c ζ τ → ∀ x y, Ψ x - y ∈ JP W T π' Eπ h' M c →
    ∀ (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a z →
    ∀ (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ), i < k + 4 * h' →
      W.levN T c ζ ⟨_, hk⟩ i =
        (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i

theorem quotientMk_eq_iff_sub_mem {T : LocLat G Qp LL O} {y y' : W.DD T} (hy : y ∈ LamPS W T Eπ h' c)
    (hy' : y' ∈ LamPS W T Eπ h' c) :
    mkP W T π' Eπ h' M c y hy = mkP W T π' Eπ h' M c y' hy' ↔ y - y' ∈ JP W T π' Eπ h' M c :=
  Submodule.Quotient.eq _

theorem framepf_mkLA_eq {T : LocLat G Qp LL O} {x x' : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hx' : x' ∈ LamLA W T π' Eπ h' c ⊤) :
    mkLA W T π' Eπ h' M c x hx = mkLA W T π' Eπ h' M c x' hx' ↔ x - x' ∈ JLA W T π' Eπ h' M c :=
  Submodule.Quotient.eq _


set_option maxHeartbeats 1000000 in
theorem framepf_frameA (hK : W.gamK = W.gam) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    {f t t' : LetA O n} (hfΔ : f ∈ W.AΔ) (hf : W.γA W.gamK π' = π' * f)
    (htΔ : t ∈ W.AΔ) (ht : W.γA W.gamK Eπ = Eπ * t)
    (ht'Δ : t' ∈ W.AΔ) (ht' : Eπ = W.γA W.gamK Eπ * t')
    (hex : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) :
    FrameA W Pt π' Eπ h' M σ c := by
  have hex' : ∀ T : LocLat G Qp LL O, ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (IsCrys PD T.ρ → FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) := by
    intro T
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨hh, Ψ, Φ, h1, h2, h3⟩ := hex T hT
      exact ⟨hh, Ψ, Φ, h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 0, fun _ _ => Submodule.zero_mem _, fun _ _ => Submodule.zero_mem _,
        fun h => absurd h hT⟩
  choose hh Ψ Φ hΨL hΦL hD using hex'
  let α : FrA W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp (LinearMap.codRestrict (LamPS W T Eπ h' c)
    (((Ψ T).restrictScalars O).comp (LamLA W T π' Eπ h' c ⊤).subtype) fun x => hΨL T x x.2)
  let β : FrB W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp
    (LinearMap.codRestrict (LamLA W T π' Eπ h' c ⊤)
      (((Φ T).restrictScalars O).comp (LamPS W T Eπ h' c).subtype) fun y => hΦL T y y.2)
  have hα : ∀ T x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy ↔
      Ψ T x - y ∈ JP W T π' Eπ h' M c := fun T x hx y hy =>
    quotientMk_eq_iff_sub_mem W π' Eπ h' M c (hΨL T x hx) hy
  have hβ : ∀ T y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx ↔
      Φ T y - x ∈ JLA W T π' Eπ h' M c := fun T y hy x hx =>
    framepf_mkLA_eq W π' Eπ h' M c (hΦL T y hy) hx
  refine ⟨α, β, fun T hT _ => ?_, fun T₁ T₂ F hT₁ hT₂ _ _ => ?_⟩
  · have D := hD T hT
    have hΨγ := framepf_Ψα_γ π' Eπ h' M c ht'Δ ht' hu huE hΔπ u huΔ hφ (hh T)
      (by rw [hK]; exact D.hγ) (Ψ T) D.hΨ
    refine ⟨fun x hx hJ => ?_, fun y hy hJ => ?_, fun x hx y hy h => ?_, fun y hy x hx h => ?_,
      fun a ha x hx y hy h hax hay => ?_, fun a ha y hy x hx h hay hax => ?_,
      fun x hx y hy h hgx hgy => ?_, fun y hy x hx h hgy hgx => ?_,
      fun τ ζ hpt x hx y hy h => D.loc τ ζ hpt x y ((hα T x hx y hy).1 h)⟩
    · exact (hα T x hx 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΨJ x hJ)
    · exact (hβ T y hy 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΦJ y hJ)
    · rw [hβ]
      have h1 := Submodule.sub_mem _ (D.βα x hx) (D.ΦJ _ ((hα T x hx y hy).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα]
      have h1 := Submodule.sub_mem _ (D.αβ y hy) (D.ΨJ _ ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα, framepf_Ψ_smulLA, ← smul_sub]
      exact framepf_JP_smul π' Eπ h' M c ha ((hα T x hx y hy).1 h)
    · rw [hβ, ← algebraMap_smul W.EE a y, map_smul, ← framepf_smulLA_alg, ← map_sub]
      exact framepf_JLA_smul π' Eπ h' M c ha ((hβ T y hy x hx).1 h)
    · rw [hα]
      have h1 := Submodule.sub_mem _
        (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht ((hα T x hx y hy).1 h)) (hΨγ x hx)
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hβ]
      have h1 := Submodule.add_mem _
        (framepf_Ψβ_γ π' Eπ h' M c hfΔ hf htΔ ht ht'Δ ht' (Ψ T) (Φ T) _ hΨγ (hΦL T) D.ΦJ D.αβ D.βα
          D.sat y hy hgy)
        (framepf_γ_JLA π' Eπ h' M c hfΔ hf htΔ ht ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_add_sub_cancel] at h1
      exact h1
  · have D₁ := hD T₁ hT₁
    have D₂ := hD T₂ hT₂
    have hFN := W.map_N F hT₁ hT₂
    have hnat := framepf_Ψα_nat F hFN π' Eπ h' M c hu huE hΔπ u huΔ hφ (hh T₁) (hh T₂)
      (framepf_hh_nat F hFN π' c M _ D₂.inj (hh T₁) (hh T₂) D₁.hγ D₂.hγ D₁.hmod D₂.hmod)
      (Ψ T₁) D₁.hΨ (Ψ T₂) D₂.hΨ
    refine ⟨fun x₁ hx₁ x₂ hx₂ y₁ hy₁ hy₂ hov h => ?_, fun y₁ hy₁ hy₂ x₁ hx₁ x₂ hx₂ hov h => ?_⟩
    · rw [hα]
      exact framepf_α_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat x₁ hx₁ x₂ y₁ hov
        ((hα T₁ x₁ hx₁ y₁ hy₁).1 h)
    · rw [hβ]
      exact framepf_β_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat (Φ T₁) (Φ T₂) _ (hΦL T₁) (hΦL T₂)
        D₂.ΦJ D₁.αβ D₂.βα D₂.sat y₁ hy₁ hy₂ x₁ x₂ hov ((hβ T₁ y₁ hy₁ x₁ hx₁).1 h)

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfF
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem modelF_local (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) (hM : 1 ≤ M)
    (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    {u u' : LetA O n} (hu' : u' ∈ W.AΔ) (huu : u' * u = 1) (hγE : W.γA W.gamK Eπ = u * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T)
    (hNP : ∀ y ∈ NcS W T c, y ∈ LamPS W T Eπ h' c) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt) :
    ModelF W T Pt π' Eπ h' M c α β := by
  have F := hfr.1 T hcry hjmp

  have C1 : ∀ x hx, x ∈ NL W T Pt π' Eπ h' c →
      ∃ y hy, y ∈ NcS W T c ∧ α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy := by
    intro x hx hxNL
    induction hxNL using Submodule.span_induction with
    | mem x hxS =>
      obtain ⟨⟨y0, hy0⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (α T ⟨x, hx⟩)
      have hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0 := hq.symm
      have hN := alpha_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww hQ h5a hp4 hpt hexp
        x hx hxS y0 hy0 hα
      obtain ⟨-, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
      exact ⟨y0, hy0, (mem_NcS W T c y0).2 ⟨hN, h2, h3⟩, hα⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
      have e : (⟨0, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = 0 := rfl
      rw [e, map_zero]
      exact (Submodule.Quotient.mk_zero _).symm
    | add x₁ x₂ h₁ h₂ ih₁ ih₂ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      have hx₂ := NL_le_LamLA W T π' Eπ h' c Pt h₂
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      obtain ⟨y₂, hy₂, hN₂, e₂⟩ := ih₂ hx₂
      refine ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, Submodule.add_mem _ hN₁ hN₂, ?_⟩
      have e : (⟨x₁ + x₂, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ := rfl
      rw [e, map_add (f := _), e₁, e₂]
      exact (Submodule.Quotient.mk_add _).symm
    | smul r x₁ h₁ ih₁ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      refine ⟨r • y₁, Submodule.smul_mem _ _ hy₁, Submodule.smul_mem _ _ hN₁, ?_⟩
      have e : (⟨r • x₁, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = r • ⟨x₁, hx₁⟩ := rfl
      rw [e, map_smul, e₁]
      exact (Submodule.Quotient.mk_smul _ _ _).symm

  have C2 : ∀ y hy, y ∈ NcS W T c →
      ∃ x hx, x ∈ NL W T Pt π' Eπ h' c ∧ β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx := by
    intro y hy hyN
    obtain ⟨⟨x, hx⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (β T ⟨y, hy⟩)
    exact ⟨x, hx, Submodule.subset_span (beta_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww
      hQ hp4 hpt y hy ((mem_NcS W T c y).1 hyN).1 x hx hq.symm), hq.symm⟩

  have HighestWeightSpaceFinite : ∀ j : ℕ, j ≤ M → ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      x ∈ piNL W T Pt π' Eπ h' c j → y ∈ PiNS W T π' j := by
    intro j hjM x hx y hy hα hpi
    obtain ⟨x', hx'NL, rfl⟩ := Submodule.mem_map.1 hpi
    have hx'L := NL_le_LamLA W T π' Eπ h' c Pt hx'NL
    obtain ⟨y', hy', hy'N, hα'⟩ := C1 x' hx'L hx'NL
    have hay := LamPS_smul W T Eπ h' c (W.AΔ.pow_mem hπΔ j) hy'
    have h2 := F.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) x' hx'L y' hy' hα' hx hay
    rw [hα] at h2
    have hd : y - π' ^ j • y' ∈ JP W T π' Eπ h' M c := by
      have h2' : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(LamPS W T Eπ h' c)) : QLamP W T π' Eπ h' M c) =
          Submodule.Quotient.mk ⟨π' ^ j • y', hay⟩ := h2
      have := (Submodule.Quotient.eq
        ((JP W T π' Eπ h' M c).comap (LamPS W T Eπ h' c).subtype)).1 h2'
      exact this
    obtain ⟨z, hzN, hz⟩ := JP_mem W T π' Eπ h' c hww hQ h5a M j hjM hd
    rw [mem_PiNS]
    refine ⟨⟨y' + z, Submodule.add_mem _ ((mem_NcS W T c y').1 hy'N).1 hzN, ?_⟩,
      ((mem_LamPS W T Eπ h' c y).1 hy).2.1⟩
    rw [smul_add, ← hz]
    abel

  have HighestWeightIntegral : ∀ j : ℕ, j ≤ M → ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      y ∈ PiNS W T π' j → x ∈ piNL W T Pt π' Eπ h' c j := by
    intro j hjM y hy x hx hβ hpi
    obtain ⟨⟨y1, hy1N, rfl⟩, -⟩ := (mem_PiNS W T π' j _).1 hpi
    have hunit : IsUnit (algebraMap (LetA O n) W.EE (π' ^ j)) := by
      rw [map_pow]
      exact hπu.pow j
    obtain ⟨-, hyΔ, hyc⟩ := (mem_LamPS W T Eπ h' c _).1 hy
    have hy1Δ : ∀ δ ∈ W.DelF, W.γD T δ y1 = y1 := by
      intro δ hδ
      have e : W.γD T δ (π' ^ j • y1) = π' ^ j • W.γD T δ y1 := by
        rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, W.AΔ.pow_mem hπΔ j δ hδ]
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, ← e, hyΔ δ hδ, sub_self]
    have hy1c : (letE c : LetA O n) • y1 = y1 := by
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, smul_comm, hyc, sub_self]
    have hy1Nc : y1 ∈ NcS W T c := (mem_NcS W T c y1).2 ⟨hy1N, hy1Δ, hy1c⟩
    have hy1L := hNP y1 hy1Nc
    obtain ⟨x1, hx1, hx1NL, hβ1⟩ := C2 y1 hy1L hy1Nc
    have hax := LamLA_smul W T π' Eπ h' c (W.AΔ.pow_mem hπΔ j) hx1
    have h6 := F.2.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) y1 hy1L x1 hx1 hβ1 hy hax
    rw [hβ] at h6
    have hd : x - smulLA W T π' c (π' ^ j) x1 ∈ JLA W T π' Eπ h' M c := by
      have h6' : (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) :
          QLamLA W T π' Eπ h' M c) = Submodule.Quotient.mk ⟨smulLA W T π' c (π' ^ j) x1, hax⟩ := h6
      have := (Submodule.Quotient.eq
        ((JLA W T π' Eπ h' M c).comap (LamLA W T π' Eπ h' c ⊤).subtype)).1 h6'
      exact this
    have h1 := JLA_le W T Pt π' Eπ h' M c hs hww hQ hp4 hpt hjmp hπΔ hEΔ j hjM hd
    have h2 : smulLA W T π' c (π' ^ j) x1 ∈ piNL W T Pt π' Eπ h' c j :=
      Submodule.mem_map_of_mem hx1NL
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  refine ⟨C1, C2, fun j _ hjM => ⟨HighestWeightSpaceFinite j hjM, HighestWeightIntegral j hjM⟩, ?_, ?_⟩
  · intro x hx y hy hα hinv
    have hγx : ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1 :=
      (Submodule.mem_inf.1 hinv).2
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hγx
    refine (mem_InvS W T π' Eπ h' 1 c y).2 ⟨hy, ?_⟩
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h7 := F.2.2.2.2.2.2.1 x hx y hy hα hgx hgy
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hα' : α T ⟨_, hsx⟩ = mkP W T π' Eπ h' M c _ hsy := by
      have e : (⟨_, hsx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨_, hgx⟩ - ⟨x, hx⟩ := rfl
      rw [e, map_sub, h7, hα]
      exact (Submodule.Quotient.mk_sub _).symm
    exact HighestWeightSpaceFinite 1 hM _ hsx _ hsy hα' hγx
  · intro y hy x hx hβ hinv
    have hγy := ((mem_InvS W T π' Eπ h' 1 c y).1 hinv).2
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h8 := F.2.2.2.2.2.2.2.1 y hy x hx hβ hgy hgx
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hβ' : β T ⟨_, hsy⟩ = mkLA W T π' Eπ h' M c _ hsx := by
      have e : (⟨_, hsy⟩ : ↥(LamPS W T Eπ h' c)) = ⟨_, hgy⟩ - ⟨y, hy⟩ := rfl
      rw [e, map_sub, h8, hβ]
      exact (Submodule.Quotient.mk_sub _).symm
    have h := HighestWeightIntegral 1 hM _ hsy _ hsx hβ' hγy
    refine Submodule.mem_inf.2 ⟨hx, ?_⟩
    show ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact h

end Local

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftValuationPoints
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  exact u1r2_basis D HW F Cm hA hl K LL hG π' E hp9 T hT c

theorem universal_lift_valuation (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    (∀ x y, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) → y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (x + y) = valAt ((HW l).W K 1 LL hG) T c ζ x + valAt ((HW l).W K 1 LL hG) T c ζ y) ∧
    (∀ (a : ↥(OL LL)) x, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (a • x) = algebraMap ↥(OL LL) ↥LL.1 a • valAt ((HW l).W K 1 LL hG) T c ζ x) := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  exact ⟨fun x y hx hy => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_add ⟨x, hx⟩ ⟨y, hy⟩,
    fun a x hx => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_smul a ⟨x, hx⟩⟩

theorem universal_lift_valuation_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ ζ' : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (hpt' : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ' τ)
    (x : ((HW l).W K 1 LL hG).DD T) (hx : x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) :
    valAt ((HW l).W K 1 LL hG) T c ζ x = valAt ((HW l).W K 1 LL hG) T c ζ' x := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  have hP' := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ' hpt'
  have hxN := ((mem_NcS _ T (c - 1) x).1 hx).1
  exact (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP ⟨x, hxN⟩).trans
    (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP' ⟨x, hxN⟩).symm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

