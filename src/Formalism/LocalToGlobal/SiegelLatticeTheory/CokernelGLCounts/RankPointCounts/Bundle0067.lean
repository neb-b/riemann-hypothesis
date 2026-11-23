module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSub
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG6

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_bwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    Prod.map φ' φ '' H.iotaGraph g t₁ ⊆ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
  rintro _ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  have hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩),
      φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c := by
    rw [← hG]
    exact ⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩
  obtain ⟨u, u', u'', hu, hu', huu, hpe2⟩ := hmemG
  simp only [Prod.mk.injEq] at hpe2
  obtain ⟨e1, e2, e3, e4⟩ := hpe2
  have key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'),
      θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂ := by
    intro m n v hmn hv
    obtain ⟨w, hw1, hw2⟩ := (D.hθ m n).1 hmn
    have h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
      have : ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w) := by
        rw [Submodule.coe_sub]
        abel
      rw [this]
      exact t₁.abelian₂.sub_mem hv hw1
    have h2 := (D.hth (v - w)).1 h1
    have : (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w)) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [this]
    exact Λ₂.add_mem hw2 h2
  have hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂ :=
    key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by
      show a + b ∈ _
      rw [hab]
      exact hx₁L)
  have hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂ :=
    key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by
      show a'' + b'' ∈ _
      rw [hab'']
      exact hl)
  have hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩ :=
    Subtype.ext (by
      show b' = b - c • b''
      rw [← hdb]
      abel)
  have hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ ⟨b', hb'⟩) =
        ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hx₂ (hcx _ hx₂'')
  have hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)
  have hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) =
        c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hx₂'', rfl⟩
  have hy : a + b ∈ H.perp (H.X t₁.f) := by
    rw [hab]
    exact x₁.2
  have hy' : a' + b' ∈ H.perp (H.X t₁.f') := by
    rw [hab']
    exact x₁'.2
  have hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) =
      H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := D.hC1 ⟨b, hb⟩
  have hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) =
      H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := D.hC1' ⟨b', hb'⟩
  have hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩ := by
    calc φ (H.mkW t₁.f x₁) = φ (H.mkW t₁.f ⟨a + b, hy⟩) :=
          congrArg φ (mkW_congr H x₁.2 hy hab.symm)
      _ = H.mkW t₂.f ⟨u, hu⟩ + H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := by
          rw [mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add (f := _), e3, hC]
      _ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm
  have hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩ := by
    calc φ' (H.mkW t₁.f' x₁') = φ' (H.mkW t₁.f' ⟨a' + b', hy'⟩) :=
          congrArg φ' (mkW_congr H x₁'.2 hy' hab'.symm)
      _ = H.mkW t₂.f' ⟨u', hu'⟩ + H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := by
          rw [mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add (f := _), e4, hC']
      _ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm
  exact ⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩

end RG6

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSup
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG7

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem add_psi_symm_mem_lam_of_theta_ddMk_eq {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (m₁ : MMsharp H t₁) (m₂ : MMsharp H t₂) (h : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂)
    (b : H.W0 t₂.f t₂.f') (hb : (m₂ : V) + (b : V) ∈ Λ₂) :
    (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := (D.hθ m₁ m₂).1 h
  have key : ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [D.hth]
    have e : ((ψ (ψ.symm b - w) : H.W0 t₂.f t₂.f') : V) = ((m₂ : V) + (b : V)) - ((m₂ : V) + ((ψ w : H.W0 t₂.f t₂.f') : V)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, Submodule.coe_sub]
      abel
    rw [e]
    exact Λ₂.sub_mem hb hw₂
  have e2 : (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) = ((m₁ : V) + (w : V)) + ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) := by
    rw [Submodule.coe_sub]
    abel
  rw [e2]
  exact t₁.abelian₂.add_mem hw₁ key

theorem rg_bwd_sup (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ ⊆ Prod.map φ' φ '' H.iotaGraph g t₁ := by
  rintro p ⟨x', x, hx'L, hxL, hdiff, rfl⟩
  obtain ⟨l, hl, hl_eq⟩ := exists_of_mem_smulLat H hdiff
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (x : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (x' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ _ ha ha' ha'' hb hb' hb'' hab hab' hab'' hl_eq
  have hxL2 : a + b ∈ Λ₂ := by rw [hab]; exact hxL
  have hx'L2 : a' + b' ∈ Λ₂ := by rw [hab']; exact hx'L
  have hlL2 : a'' + b'' ∈ Λ₂ := by rw [hab'']; exact hl
  have sa : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb hxL2
  have sa' : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' hx'L2
  have sa'' : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' hlL2
  have pa : a ∈ H.perp (H.X t₂.f) := by
    have e : a = (x : V) - b := by rw [← hab]; abel
    rw [e]
    exact Submodule.sub_mem _ x.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have pa' : a' ∈ H.perp (H.X t₂.f') := by
    have e : a' = (x' : V) - b' := by rw [← hab']; abel
    rw [e]
    exact Submodule.sub_mem _ x'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have hmem : (ddMk H t₂ ⟨a, sa⟩, ddMk H t₂ ⟨a'', sa''⟩, H.mkW t₂.f ⟨a, pa⟩, H.mkW t₂.f' ⟨a', pa'⟩) ∈
      GamR H t₂ (algebraMap F E (g.q : F)) :=
    ⟨⟨a, sa⟩, ⟨a', sa'⟩, ⟨a'', sa''⟩, pa, pa', hda, rfl⟩
  rw [← hG] at hmem
  obtain ⟨q, ⟨u, u', u'', hu, hu', hdu, rfl⟩, hq⟩ := hmem
  simp only [Prod.mk.injEq] at hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hy := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u ⟨a, sa⟩ h1 ⟨b, hb⟩ hxL2
  have hy'' := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u'' ⟨a'', sa''⟩ h2 ⟨b'', hb''⟩ hlL2
  have hn' : ψ.symm ⟨b', hb'⟩ = ψ.symm ⟨b, hb⟩ - (algebraMap F E (g.q : F)) • ψ.symm ⟨b'', hb''⟩ := by
    rw [← map_smul, ← map_sub]
    congr 1
    ext
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rw [← hdb]
    abel
  have hu'e : (u' : V) = (u : V) - (algebraMap F E (g.q : F)) • (u'' : V) := by
    rw [← hdu]; abel
  have hy'e : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) =
      ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
        (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) := by
    rw [hn', hu'e, Submodule.coe_sub, Submodule.coe_smul, smul_add]
    abel
  have py : (u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f) :=
    Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2)
  have py' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f') :=
    Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2)
  have hcy : (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) ∈ t₁.abelian₂ :=
    smul_mem_lat g t₁.abelian₂ hy''
  have hyL' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [hy'e]; exact t₁.abelian₂.sub_mem hy hcy
  have hdL : ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
      ((u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V)) ∈
      H.smulLat (algebraMap F E (g.q : F)) t₁.abelian₂ := by
    rw [hy'e, sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hy'', rfl⟩
  refine ⟨(H.mkW t₁.f' ⟨_, py'⟩, H.mkW t₁.f ⟨_, py⟩), ⟨⟨_, py'⟩, ⟨_, py⟩, hyL', hy, hdL, rfl⟩, ?_⟩
  simp only [Prod.map]
  congr 1
  · rw [mkW_add H _ _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2), map_add (f := _), h4, D.hC1',
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab'
  · rw [mkW_add H _ _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2), map_add (f := _), h3, D.hC1,
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab

end RG7

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSub
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG4

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_fwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hI : Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩) :
    (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) ⊆
      GamR H t₂ (algebraMap F E (g.q : F)) := by
  set c : E := algebraMap F E (g.q : F) with hc
  have hcO : c ∈ M.L.O := q_mem_O g
  have hcL : ∀ (Λ : Submodule M.L.O V) {x : V}, x ∈ Λ → c • x ∈ Λ := by
    intro Λ x hx
    exact Λ.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  have hMMU : ∀ (t : Term V M r) {x : V}, x ∈ MMsharp H t →
      x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
    intro t x hx
    have h1 : x ∈ Submodule.span E (Set.range (H.MMfam t)) := hx.1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨i, rfl⟩
    have hle : H.Xp t.f ⊔ H.Xp t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
      sup_le
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inl j, rfl⟩))
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inr j, rfl⟩))
    exact hle (MMfam_mem_sup H t i)
  rintro _ ⟨p, ⟨u, u', u'', hu, hu', hd, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := D.hsurj₁ u
  obtain ⟨w'', hw''⟩ := D.hsurj₁ u''
  obtain ⟨w', hw'c⟩ : ∃ w' : ↥(H.W0 t₁.f t₁.f'), (w' : V) = (w : V) - c • (w'' : V) :=
    ⟨w - c • w'', rfl⟩
  have hw'eq : w' = w - c • w'' := Subtype.ext (by rw [hw'c]; rfl)
  have hψw' : (ψ w' : V) = (ψ w : V) - c • (ψ w'' : V) := by
    rw [hw'eq, map_sub, map_smul]
    rfl
  have hx : (u : V) + w ∈ H.perp (H.X t₁.f) := Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H w.2)
  have hx' : (u' : V) + w' ∈ H.perp (H.X t₁.f') := Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H w'.2)
  have hxL' : (u' : V) + w' ∈ t₁.abelian₂ := by
    have e : (u' : V) + w' = ((u : V) + w) - c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.sub_mem _ hw (hcL _ hw'')
  have hdiffL : ((u : V) + w) - ((u' : V) + w') ∈ H.smulLat c t₁.abelian₂ := by
    have e : ((u : V) + w) - ((u' : V) + w') = c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hw'', rfl⟩
  have hmem : (φ' (H.mkW t₁.f' ⟨_, hx'⟩), φ (H.mkW t₁.f ⟨_, hx⟩)) ∈
      H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
    rw [← hI]
    exact ⟨_, ⟨⟨_, hx'⟩, ⟨_, hx⟩, hxL', hw, hdiffL, rfl⟩, rfl⟩
  obtain ⟨y', y, hy'L, hyL, hyd, hyeq⟩ := hmem
  rw [Prod.mk.injEq] at hyeq
  obtain ⟨hyeq', hyeq2⟩ := hyeq
  obtain ⟨z, hzL, hz⟩ := exists_of_mem_smulLat H hyd
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (y : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (y' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ z
  have hx₂ : a + b ∈ H.perp (H.X t₂.f) := by
    rw [hab]
    exact y.2
  have hx₂' : a' + b' ∈ H.perp (H.X t₂.f') := by
    rw [hab']
    exact y'.2
  have hap : a ∈ H.perp (H.X t₂.f) := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp H hb) hx₂
  have hap' : a' ∈ H.perp (H.X t₂.f') := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp' H hb') hx₂'
  have h1 : φ (H.mkW t₁.f ⟨_, hx⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩ :=
    hyeq2.trans (congrArg _ (Subtype.ext hab.symm))
  have h1' : φ' (H.mkW t₁.f' ⟨_, hx'⟩) = H.mkW t₂.f' ⟨a' + b', hx₂'⟩ :=
    hyeq'.trans (congrArg _ (Subtype.ext hab'.symm))
  obtain ⟨hbψ, hφ⟩ := RGHyp.trF H D (hMMU t₁ u.2) hu w hx ha hb hap hx₂ h1
  obtain ⟨hb'ψ, hφ'⟩ := RGHyp.trF' H D (hMMU t₁ u'.2) hu' w' hx' ha' hb' hap' hx₂' h1'
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hz
  have hb''ψ : b'' = ψ w'' := by
    apply smul_cancel_q g
    rw [← hdb, hbψ, hb'ψ, hψw']
    abel
  have haM : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb (by rw [hab]; exact hyL)
  have ha'M : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' (by rw [hab']; exact hy'L)
  have ha''M : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' (by rw [hab'']; exact hzL)
  refine ⟨⟨a, haM⟩, ⟨a', ha'M⟩, ⟨a'', ha''M⟩, hap, hap', hda, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext hφ hφ'))
  · exact (D.hθ u ⟨a, haM⟩).mpr ⟨w, hw, by rw [← hbψ, hab]; exact hyL⟩
  · exact (D.hθ u'' ⟨a'', ha''M⟩).mpr ⟨w'', hw'', by rw [← hb''ψ, hab'']; exact hzL⟩

end RG4

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfEx
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def CondX (w : Point D.host.E (D.R.rS + 1)) (X : MatR D) : Prop :=
  ∀ a c : Fin (D.R.rS + 1), a < c → blkOf w.1 a.val = blkOf w.1 c.val →
    X (pinv w c) (pinv w a) ∈ ddPow D (c.val - a.val) ∧ bt D X⁻¹ a c ∈ ddPow D (c.val - a.val) ∧
      X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) ∈ qdPow D (c.val - a.val)

theorem entryShape_iff (w : Point D.host.E (D.R.rS + 1)) {β b : MatR D} (hβ : IsLoUni β) (hb : IsUpUni b)
    (hW : β * ptMat w * b = ptMat w) :
    EntryShape D β b ↔ CondX w ((ptMat w)⁻¹ * β * ptMat w) := by
  obtain ⟨hXb, hX, hXB⟩ := X_of_st w hβ hb hW
  set X := (ptMat w)⁻¹ * β * ptMat w with hXdef
  have hbX : b = X⁻¹ := by
    rw [hXb, Matrix.nonsing_inv_nonsing_inv _ (by rw [upU_det hb]; exact isUnit_one)]

  have hβX : β = ptMat w * X * (ptMat w)⁻¹ := by
    have hu := ptMat_isUnit w
    rw [hXdef, show ptMat w * ((ptMat w)⁻¹ * β * ptMat w) * (ptMat w)⁻¹ =
      (ptMat w * (ptMat w)⁻¹) * β * (ptMat w * (ptMat w)⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hβij : ∀ i j, β i j = cv w i * X (pinv w i) (pinv w j) * (cv w j)⁻¹ := by
    intro i j; rw [hβX, conj'_apply]

  have hXiB : IsBlockDiagonalMatrix w X⁻¹ := by
    have hβi : IsLoUni β⁻¹ := by
      have := loU_inv (show LoU β from hβ); exact this
    have hW' : β⁻¹ * ptMat w * X = ptMat w := by
      have hu := ptMat_isUnit w
      have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hβ)]; exact isUnit_one
      rw [hXdef, show β⁻¹ * ptMat w * ((ptMat w)⁻¹ * β * ptMat w) = β⁻¹ * (ptMat w * (ptMat w)⁻¹) * β * ptMat w by
        simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hβd,
        Matrix.one_mul]
    obtain ⟨h1, -, h3⟩ := X_of_st w hβi hX hW'
    have hXi : (ptMat w)⁻¹ * β⁻¹ * ptMat w = X⁻¹ := h1
    rw [← hXi]; exact h3
  rw [hbX]
  constructor
  · intro h a c hac hs
    obtain ⟨h1, h2, h3⟩ := h c a hac
    have hcv : cv w c = cv w a := (pval_eq_blk w a c hs).symm
    have key : ∀ x : D.host.E, cv w a * (x * (cv w a)⁻¹) = x := fun x => by
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w a), one_mul]
    rw [hβij, hcv, mul_assoc, key] at h1 h3
    exact ⟨h1, h2, h3⟩
  · intro h i j hji
    by_cases hs : blkOf w.1 j.val = blkOf w.1 i.val
    · obtain ⟨h1, h2, h3⟩ := h j i hji hs
      have hcv : cv w i = cv w j := (pval_eq_blk w j i hs).symm
      have key : ∀ x : D.host.E, cv w j * (x * (cv w j)⁻¹) = x := fun x => by
        rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w j), one_mul]
      rw [hβij, hcv, mul_assoc, key]
      exact ⟨h1, h2, h3⟩
    · have hs' : blkOf w.1 (pinv w i).val ≠ blkOf w.1 (pinv w j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      have hb0 : X⁻¹ j i = 0 := hXiB j i hs
      have hbt : bt D X⁻¹ j i = 0 := by simp [bt, hb0]
      rw [hβij, hXB _ _ hs', mul_zero, zero_mul, hbt, map_zero, sub_zero]
      exact ⟨FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _⟩

theorem mem_stabInt_iff_X (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔ CondX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) := by
  rw [stabIntShape D δ M hA u u' w β]
  constructor
  · rintro ⟨-, b', hb', hW', hE⟩
    exact (entryShape_iff w hβ hb' hW').1 hE
  · intro h
    exact ⟨hβ, b, hb, hW, (entryShape_iff w hβ hb hW).2 h⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

