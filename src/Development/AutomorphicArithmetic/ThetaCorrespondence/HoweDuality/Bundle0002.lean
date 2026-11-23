module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerV
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerV :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om v ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hT := hM.triple
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hM.fin.inv v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    have hx' : Rf.p v (x : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0 := hx
    have h0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have ht : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext y; simp [tens]
      rw [ht, map_zero]
    have e := hM.fin.equiv v h hh x x.2 0 (zero_mem _) (g x) (g x).2 0 (zero_mem _) (hg x) h0
      (by rw [hx', map_zero])
    show Rf.p v ((g x : SB _) : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0
    rw [e, map_zero]
  · intro hKe
    have hbot : (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      have hm : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈
          LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
        rw [hKe]; exact Submodule.mem_top
      exact hm
    rw [hM.fin.onto v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  · intro N hKN hst hne
    have key : ∀ x : SB (Fin a × Fin (a + a') → Fv F v),
        Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) → x ∈ N := by
      rintro x ⟨_, ⟨n, hn, rfl⟩, hpn⟩
      have hk : x - n ∈ N := hKN (by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact hpn.symm)
      have := N.add_mem hn hk
      rwa [add_sub_cancel] at this
    rcases hM.fin.irred v ((N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v)) (by
      intro h hh ψ hψ ψ₁ hψ₁ hact hpm
      have hx : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈ N := key ⟨ψ, hψ⟩ hpm
      have e := GlobalTheory.ThK.LocalOps.acts_unique v _ hψ hact (GlobalTheory.HoweGlobal.FinPlace.locOp_acts hT v hh ⟨ψ, hψ⟩)
      exact Submodule.mem_map_of_mem ⟨GlobalTheory.HoweGlobal.FinPlace.locOp hT v hh ⟨ψ, hψ⟩,
        hst _ (GlobalTheory.HoweGlobal.FinPlace.locOp_mem hT v hh) _ hx, e.symm⟩) with h0 | htop
    · intro x hx
      have hmem : Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) :=
        Submodule.mem_map_of_mem ⟨x, hx, rfl⟩
      rw [h0] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem
    · exfalso
      apply hne
      rw [Submodule.eq_top_iff']
      intro x
      apply key
      rw [htop]; exact Submodule.mem_top
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerVp
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerVp :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om' v ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om' v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hz : ∀ (h : UA σ G.W.J), Acts (evFin F v) (om (1, h))
      (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro h r _
    have h0 : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x
      simp [tens]
    rw [h0, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact hM.fin.inv' v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    have e := hM.fin.equiv v h hh 0 (Submodule.zero_mem _) x x.2 0 (Submodule.zero_mem _)
      (g x) (g x).2 (hz h) (hg x) (by rw [map_zero]; exact hx.symm)
    rw [map_zero] at e
    exact e.symm
  · intro hK
    haveI := hM.fin.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hmem : y ∈ Submodule.map (Rf.p' v) (SB (Fin a' × Fin (a + a') → Fv F v)) := by
      rw [hM.fin.onto' v]
      exact Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := hmem
    have hk : (⟨φ, hφ⟩ : SB (Fin a' × Fin (a + a') → Fv F v)) ∈
        LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
      rw [hK]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    exact hy hk
  · intro N hKN hN hNtop
    have hst : ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
            Acts (evFin F v) (om (1, h)) φ φ₁ →
              Rf.p v φ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) →
              Rf.p v φ₁ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
      intro h hh φ hφ φ₁ hφ₁ hact hp
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hp
      have hgn := hN _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_mem hM.triple v hh) n hn
      have e := hM.fin.equiv v h hh φ hφ n n.2 φ₁ hφ₁ _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp hM.triple v hh n).2
        hact (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_acts hM.triple v hh n) hpn.symm
      exact ⟨_, ⟨_, hgn, rfl⟩, e.symm⟩
    rcases hM.fin.irred v _ hst with hbot | htop
    · intro x hx
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) :=
        ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hm
    · exfalso
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hm
      have hk : x - n ∈ N := by
        apply hKN
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub, map_sub, sub_eq_zero]
        exact hpn.symm
      have := N.add_mem hk hn
      rwa [sub_add_cancel] at this
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadIrr
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radIrr :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.IrrAt om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P →
      Stable (opFin om v) P → P = relFin om v ∨ P = ⊤ := by
    intro P hP hPs
    have hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        have hzS := aug_le hz
        refine ⟨⟨z, hzS⟩, hP ?_, rfl⟩
        simpa [relFin] using hz
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA
        have hφ₁eq : φ₁ = ω (1, h) k := (hL.acts 1 one_mem h hh k k.2 φ₁).mp hA
        let g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
          { toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
            map_add' := fun x y => by ext1; simp
            map_smul' := fun c x => by ext1; simp }
        have hg : g ∈ opFin om v := by
          refine ⟨h, hh, fun φ => ?_⟩
          exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
        refine ⟨g k, hPs g hg k hk, ?_⟩
        simp [g, hφ₁eq]
    rcases hI _ hT with h1 | h1
    · left
      ext x
      constructor
      · intro hx
        have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := by
          rw [← h1]
          exact ⟨x, hx, rfl⟩
        simpa [relFin] using hx'
      · intro hx
        exact hP hx
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
        rw [h1]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hK : K = relFin om v := by
    rcases key K hrel hst with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by
    by_contra hc
    push_neg at hc
    apply hne
    rw [hK, eq_top_iff]
    intro x _
    exact hc x
  refine ⟨s, ?_, ?_⟩
  · intro P hP hPs hsP
    rcases key P hP hPs with h | h
    · rw [h] at hsP
      exact absurd hsP hs
    · exact h
  · intro k hk
    refine ⟨1, Subalgebra.one_mem _, rfl, ?_⟩
    rw [hK] at hk
    simpa using hk
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadSph
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radSph :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.SphAt M ψ om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hS K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hG : ∀ h ∈ UAt σ W (evFin F v), ∃ g ∈ opFin om v,
      ∀ x : ↥(SB (Fin n × Fin d → Fv F v)), (g x : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) x := by
    intro h hh
    refine ⟨{ toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
              map_add' := fun x y => by ext1; simp
              map_smul' := fun c x => by ext1; simp }, ⟨h, hh, fun φ => ?_⟩, fun x => rfl⟩
    exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
  choose g hgOp hgapp using hG
  obtain ⟨s, hs⟩ := hS ω ρ hL
  let s' : ↥(SB (Fin n × Fin d → Fv F v)) := ⟨s, hs.mem⟩
  have hgen : Gen (opFin om v) (relFin om v) s' := by
    intro P hP hPs hsP
    have hle : augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s} ≤
        P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
      refine sup_le ?_ ?_
      · intro z hz
        exact ⟨⟨z, aug_le hz⟩, hP hz, rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro z ⟨h, hh, rfl⟩
        exact ⟨g h hh s', hPs _ (hgOp h hh) _ hsP, hgapp h hh s'⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle (hs.gen x x.2)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  refine ⟨s', hgen, ?_⟩
  intro k hk
  obtain ⟨m, kk, w, c, hkw, hsum⟩ := hs.line k k.2
  let e : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
    ((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1
  have he_app : ∀ x : ↥(SB (Fin n × Fin d → Fv F v)),
      (e x : (Fin n × Fin d → Fv F v) → ℂ) = ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) x := by
    intro x
    simp [e, hgapp]
  have hm : (m + 1 : ℂ) ≠ 0 := by
    norm_cast
  have hes : e s' = s' := by
    ext1
    rw [he_app]
    have hsum' : ∑ i : Fin (m + 1), w i • ω (1, kk i) s = ∑ _i : Fin (m + 1), s :=
      Finset.sum_congr rfl (fun i _ => (hkw i).2)
    show ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) s = s
    rw [hsum', Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hm, one_smul]
  have heK : e k ∈ K := by
    show (((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1) k ∈ K
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    refine K.smul_mem _ (K.sum_mem fun i _ => ?_)
    rw [LinearMap.smul_apply]
    exact K.smul_mem _ (hst _ (hgOp _ _) k hk)
  have hrelv : e k - (((m + 1 : ℂ))⁻¹ * c) • s' ∈ relFin om v := by
    show ((e k - (((m + 1 : ℂ))⁻¹ * c) • s' : ↥(SB (Fin n × Fin d → Fv F v))) :
      (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
    rw [Submodule.coe_sub, Submodule.coe_smul, he_app]
    have hh := (augAt om v).smul_mem ((m + 1 : ℂ))⁻¹ hsum
    rw [smul_sub, smul_smul] at hh
    exact hh
  by_cases hc : ((m + 1 : ℂ))⁻¹ * c = 0
  · refine ⟨e, ?_, hes, ?_⟩
    · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (hgOp _ _)) _) _
    · rw [hc, zero_smul, sub_zero] at hrelv
      exact hrelv
  · exfalso
    apply hne
    apply hgen K hrel hst
    have h1 : (((m + 1 : ℂ))⁻¹ * c) • s' ∈ K := by
      have h2 := K.sub_mem heK (hrel hrelv)
      rwa [sub_sub_cancel] at h2
    have h3 := K.smul_mem (((m + 1 : ℂ))⁻¹ * c)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RelStable
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.relStable :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → Stable (opFin om v) (relFin om v) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL g hg x hx
  obtain ⟨h, hh, hact⟩ := hg
  have h1X : (1 : UA σ X.J) ∈ UAt σ X ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ X.J) - 1)
    intro u _
    rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  have h1W : (1 : UA σ W.J) ∈ UAt σ W ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ W.J) - 1)
    intro u _
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have hgx : ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) (x : (Fin n × Fin d → Fv F v) → ℂ) :=
    (hL.acts 1 h1X h hh x x.2 _).1 (hact x)
  have key : augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
    have e1 : φ₁ = ω (g', 1) φ := (hL.acts g' hg' 1 h1W φ hφ φ₁).1 hA
    subst e1
    have m1 := hL.mul 1 h1X h hh g' hg' 1 h1W φ hφ
    have m2 := hL.mul g' hg' 1 h1W 1 h1X h hh φ hφ
    simp only [one_mul, mul_one] at m1 m2
    have hp : ω (1, h) φ ∈ SB (Fin n × Fin d → Fv F v) := hL.pres 1 h1X h hh φ hφ
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    rw [← m1, m2]
    exact Submodule.subset_span ⟨g', hg', ω (1, h) φ, hp, ω (g', 1) (ω (1, h) φ),
      hL.pres g' hg' 1 h1W _ hp, (hL.acts g' hg' 1 h1W _ hp _).2 rfl, rfl⟩
  have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := hx
  show ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
  rw [hgx]
  exact key hx'
end

