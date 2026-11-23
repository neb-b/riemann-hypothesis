module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsRingChange

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeIndep
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

def mapE {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq) (e : Edge W Qq k) :
    Edge W Qq k := ⟨e.src.map (nt_phi W g), e.tgt.map (nt_phi W g)⟩

theorem mapE_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq)
    (e : Edge W Qq k) : mapE g (mapE g⁻¹ e) = e := by
  have hid : (nt_phi W g).comp (nt_phi W g⁻¹) = LinearMap.id := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, LinearMap.id_apply]
  cases e with
  | mk src tgt =>
    simp only [mapE, Edge.mk.injEq]
    constructor <;> rw [← Submodule.map_comp, hid, Submodule.map_id]

def RestFunct : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ g : GL (Fin (m + 1)) R.Qq, ∃ T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0,
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        ∀ x, x ∈ HL (O := R.O) R.ι R.σ lam0 L ↔ T x ∈ HL (O := R.O) R.ι R.σ lam0 (L.map (nt_phi R.W g))) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        ∀ x, x ∈ HLe p R.ι R.σ R.w lam0 e ↔ T x ∈ HLe p R.ι R.σ R.w lam0 (mapE g e))

section Formal

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

theorem scale_alt (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c M) : T x ∈ scale c M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨T y, (h y).1 hy, by simp⟩

theorem comp_symm_mem_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {φ : Module.Dual Kf V}
    (hφ : φ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M) : φ.comp T.symm.toLinearMap ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M' := by
  intro v hv
  exact hφ (T.symm v) ((h _).2 (by rwa [LinearEquiv.apply_symm_apply]))

theorem comp_symm_mem_scale_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M)) :
    φ.comp T.symm.toLinearMap ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M') := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_dualLat_of_mem_iff T h hψ, by ext v; simp⟩

theorem apply_mem_scale_scale_of_mem_iff (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c (scale d M)) : T x ∈ scale c (scale d M') := by
  have hs : ∀ y, y ∈ M' ↔ T.symm y ∈ M := fun y => by rw [h (T.symm y), LinearEquiv.apply_symm_apply]
  have hiff : ∀ y, y ∈ scale d M ↔ T y ∈ scale d M' := fun y =>
    ⟨fun hy => scale_alt T d h hy, fun hy => by
      have := scale_alt T.symm d hs hy
      rwa [LinearEquiv.symm_apply_apply] at this⟩
  exact scale_alt T c hiff hx

theorem scaled_dual_lattice_transport (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M))) :
    φ.comp T.symm.toLinearMap ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M')) := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_scale_dualLat_of_mem_iff T d h hψ, by ext v; simp⟩

end Formal

theorem restEdge_of (hFun : RestFunct) : RestEdge := by
  classical
  intro p n' R m lam0 hDom t c n D e e' he he' hfac
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  have htgtC : ∀ y, y ∈ CCL' R lam0 t c e → y.comp T.symm.toLinearMap ∈ CCL' R lam0 t c (mapE γ e) := by
    intro y hy
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT1 e.tgt he.2.1) hy.1.1
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) hy.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').tgt = e.tgt := by
        show e''.tgt.map (nt_phi R.W γ⁻¹) = e.tgt
        rw [h2]
        exact nt_map_inv γ e.tgt
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL'_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hy
      have h7 := scaled_dual_lattice_transport T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => htgtC _ (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfIndex
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def othW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then 0 else lam0 s

def Pr {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
    [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [AddCommGroup V] [Module Kf V] [Module O V]
    (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) (M : Submodule O V₁) (N : Submodule O V₂) : Submodule O V :=
  Submodule.span O {x | ∃ F ∈ M, ∃ r ∈ N, x = μ F r}

def RestTensor : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∃ (μ : Vsp R.Kf (topW TT lam0) →ₗ[R.Kf] Vsp R.Kf (othW TT lam0) →ₗ[R.Kf] Vsp R.Kf lam0)
      (ν : Module.Dual R.Kf (Vsp R.Kf (topW TT lam0)) →ₗ[R.Kf] Module.Dual R.Kf (Vsp R.Kf (othW TT lam0)) →ₗ[R.Kf]
        Module.Dual R.Kf (Vsp R.Kf lam0)),
      (∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) ∧
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        HL (O := R.O) R.ι R.σ lam0 L =
          Pr μ (HL (O := R.O) R.ι R.σ (topW TT lam0) L) (HL (O := R.O) R.ι R.σ (othW TT lam0) L)) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        HLe p R.ι R.σ R.w lam0 e =
          Pr μ (HLe p R.ι R.σ R.w (topW TT lam0) e) (HLe p R.ι R.σ R.w (othW TT lam0) e)) ∧
      dimV R.Kf lam0 = dimV R.Kf (topW TT lam0) * dimV R.Kf (othW TT lam0)

def RestOrdBound : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ), IsDominant lamO →
    (∀ s i, |lamO s i| ≤ c) → ∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
      Re p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ))) (HL R.ι R.σ lamO e.src) ∧
      Re' p R.ι R.σ R.w 1 lamO e ≤
        scale (algebraMap R.O R.Kf R.w ^ (-((2 * n' * c : ℕ) : ℤ)))
          (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (HL (O := R.O) R.ι R.σ lamO e.tgt))

section Formal

variable {O Kf V₁ V₂ V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V₁] [Module Kf V₁] [Module O V₁]
  [IsScalarTower O Kf V₁] [AddCommGroup V₂] [Module Kf V₂] [Module O V₂] [IsScalarTower O Kf V₂] [AddCommGroup V]
  [Module Kf V] [Module O V] [IsScalarTower O Kf V]

theorem scale_mono (c : Kf) {M M' : Submodule O V} (h : M ≤ M') : scale c M ≤ scale c M' := Submodule.map_mono h

theorem scale_scale_mem {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale a (scale b M)) :
    x ∈ scale (a * b) M := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mem_scale_scale {a b : Kf} {M : Submodule O V} {x : V} (h : x ∈ scale (a * b) M) :
    x ∈ scale a (scale b M) := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp h
  refine Submodule.mem_map.mpr ⟨b • z, Submodule.mem_map.mpr ⟨z, hz, by simp⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem mu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂} {F : V₁} {r : V₂}
    (hF : F ∈ scale a M) (hr : r ∈ scale b N) : μ F r ∈ scale (a * b) (Pr μ M N) := by
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨r0, hr0, rfl⟩ := Submodule.mem_map.mp hr
  refine Submodule.mem_map.mpr ⟨μ F0 r0, Submodule.subset_span ⟨F0, hF0, r0, hr0, rfl⟩, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

theorem nu_dual (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M)
    (hρ : ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf N) : ν G ρ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, r, hr, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG F hF
    obtain ⟨b, hb⟩ := hρ r hr
    exact ⟨a * b, by rw [hν, map_mul, ha, hb]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, ← algebraMap_smul Kf c x, map_smul, smul_eq_mul]⟩

theorem nu_scale (μ : V₁ →ₗ[Kf] V₂ →ₗ[Kf] V)
    (ν : Module.Dual Kf V₁ →ₗ[Kf] Module.Dual Kf V₂ →ₗ[Kf] Module.Dual Kf V)
    (hν : ∀ G ρ F r, ν G ρ (μ F r) = G F * ρ r) {a b : Kf} {M : Submodule O V₁} {N : Submodule O V₂}
    {G : Module.Dual Kf V₁} {ρ : Module.Dual Kf V₂} (hG : G ∈ scale a (Formalism.GradedWeylDivisibility.dualLat O Kf M))
    (hρ : ρ ∈ scale b (Formalism.GradedWeylDivisibility.dualLat O Kf N)) :
    ν G ρ ∈ scale (a * b) (Formalism.GradedWeylDivisibility.dualLat O Kf (Pr μ M N)) := by
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hG
  obtain ⟨ρ0, hρ0, rfl⟩ := Submodule.mem_map.mp hρ
  refine Submodule.mem_map.mpr ⟨ν G0 ρ0, nu_dual μ ν hν hG0 hρ0, ?_⟩
  simp [mul_smul]
  exact smul_comm _ _ _

end Formal

theorem FactorsLE_of_index {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A : Submodule O V} {A' : Submodule O V'} {D : ℝ} {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (hcard : Fintype.card I = n) (x : I → V) (y : I → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O)
    (M : Matrix I I O) (hz : z ≠ 0) (hv : vLEO p z D)
    (hM : ∀ i j, ∑ l, be (x i) (y l) * algebraMap O Kf (M l j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' n D := by
  unfold FactorsLE
  right
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => x (e i), fun i => y (e i), fun i => hx _, fun i => hy _, z, M.submatrix e e, hz, hv, fun i j => ?_⟩
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun l => be (x (e i)) (y l) * algebraMap O Kf (M l (e j))), hM]
  simp [e.injective.eq_iff]

theorem othW_dom {n' m : ℕ} {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant lam0) :
    IsDominant (othW TT lam0) := by
  show ∀ s, Antitone (othW TT lam0 s)
  intro s
  simp only [othW]
  split_ifs
  · exact antitone_const
  · exact h s

theorem Ar_add {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Ar 1 lam0 = Ar 1 (topW TT lam0) + Ar 1 (othW TT lam0) := by
  unfold Ar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lamAt topW othW
  by_cases hs : s ∈ TT <;> by_cases he : Even (s : ℕ) <;> simp [hs, he]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HLepolyTr
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section

variable {p n' : ℕ} {R₁ R₂ : RS p n'} (I : RSIso R₁ R₂) {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem pm_symm (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) :
    I.symm.JO.pm (I.JO.pm P) = P := by
  show MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) (MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) P) = P
  have h : (I.φK.symm : R₂.Kf →+* R₁.Kf).comp (I.φK : R₁.Kf →+* R₂.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

theorem pm_symm' (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₂.Kf) :
    I.JO.pm (I.symm.JO.pm P) = P := by
  show MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) (MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) P) = P
  have h : (I.φK : R₁.Kf →+* R₂.Kf).comp (I.φK.symm : R₂.Kf →+* R₁.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

def PsiV : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0 where
  toFun x := ⟨I.JO.pm x.1, Vsp_tr I lam0 x.1 x.2⟩
  invFun y := ⟨I.symm.JO.pm y.1, Vsp_tr I.symm lam0 y.1 y.2⟩
  left_inv x := Subtype.ext (pm_symm I x.1)
  right_inv y := Subtype.ext (pm_symm' I y.1)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem HLpoly_tr (L : Submodule R₁.W (Fin (m + 1) → R₁.Qq))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => extO R₁.O R₁.ι R₁.σ s.val L)) :
    I.JO.pm P ∈ Hten R₂.O lam0 (fun s => extO R₂.O R₂.ι R₂.σ s.val (mapSub I.JW L)) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => extO R₁.O R₁.ι R₁.σ s.val L) (P := P) hP
  simp only [extO_tr] at h
  exact h

theorem HLepoly_tr (e : Edge R₁.W R₁.Qq (m + 1))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e)) :
    I.JO.pm P ∈ Hten R₂.O lam0
      (fun s => LeAt p R₂.ι R₂.σ R₂.w s.val ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e) (P := P) hP
  simp only [LeAt_tr] at h
  exact h

end

theorem restHLTransport : RestHLTransport := by
  intro p n' R₁ R₂ I m lam0
  have hΨ : ∀ (c : R₁.Kf) (v : Vsp R₁.Kf lam0), PsiV I lam0 (c • v) = I.φK c • PsiV I lam0 v := by
    intro c v
    exact Subtype.ext (map_smul' _ c v.1)
  refine ⟨mapSubEquiv I.JW, PsiV I lam0, hΨ, fun L => isLattice_mapSub_iff I.JW L, fun r e => ?_, fun L x => ?_,
    fun e x => ?_, ?_⟩
  · constructor
    · exact isEdge_mapSub I.JW p n' r
    · intro h
      have h2 := isEdge_mapSub I.JW.symm p n' r h
      simp only at h2
      have h3 : mapSub I.JW.symm (mapSub I.JW e.src) = e.src := mapSub_symm _ _
      have h4 : mapSub I.JW.symm (mapSub I.JW e.tgt) = e.tgt := mapSub_symm _ _
      have h5 : (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) = e := by rw [h3, h4]
      have h6 : IsEdge p n' r (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) := h2
      rwa [h5] at h6
  · constructor
    · intro hx
      exact HLpoly_tr I lam0 L x.1 hx
    · intro hx
      have h2 := HLpoly_tr I.symm lam0 (mapSub I.JW L) (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW L) = L := mapSub_symm I.JW L
      rw [h3] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · constructor
    · intro hx
      exact HLepoly_tr I lam0 e x.1 hx
    · intro hx
      have h2 := HLepoly_tr I.symm lam0 ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩ (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW e.src) = e.src := mapSub_symm I.JW _
      have h3' : mapSub I.symm.JW (mapSub I.JW e.tgt) = e.tgt := mapSub_symm I.JW _
      simp only [h3, h3'] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · unfold dimV Module.finrank
    rw [rank_eq_of_equiv_equiv I.φK (PsiV I lam0) I.φK.bijective hΨ]

theorem lpRingIndep_of' (h : RestRSIso) : LPRingIndep := lpRingIndep_of h restHLTransport

end Formalism.MainNotions.flipOneThree.Pf

end
end

