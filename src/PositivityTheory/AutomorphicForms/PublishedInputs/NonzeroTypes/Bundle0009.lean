module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PKill
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_kill

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem PJ_smul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (a : ℂ) (v : V) : G.PJ π r (a • v) = a • G.PJ π r v := by
  unfold Grp.PJ
  rw [smul_finsum]
  congr 1
  funext c
  rw [map_smul, smul_comm]

theorem core_mul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hmul : ∀ v : V, (∀ u ∈ KC k n r, π u v = v) → ∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v)
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 := by
  obtain ⟨j, hjJ, hyj, hne⟩ := hj
  have hx' : ∀ g ∈ G.JSet, π g x = G.lam g • x := hx
  have hjw : π j (π y x) = G.lam (y⁻¹ * j * y) • π y x := by
    have e : j * y = y * (y⁻¹ * j * y) := by group
    have e1 : π j (π y x) = π (j * y) x := by rw [map_mul]; rfl
    have e2 : π (y * (y⁻¹ * j * y)) x = π y (π (y⁻¹ * j * y) x) := by rw [map_mul]; rfl
    rw [e1, e, e2, hx' _ hyj, map_smul]
  have key := hmul (π y x) hfix j hjJ
  rw [hjw, PJ_smul] at key
  have h0 : (G.lam (y⁻¹ * j * y) - G.lam j) • G.PJ π r (π y x) = 0 := by
    rw [sub_smul, key, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hPJ : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
      ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
        G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
        (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v))
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 :=
  core_mul G π r (fun v hv => (hPJ.2 v hv).2.1) x hx y hfix hj

end UpperTheory.TNZ.Grp.P_kill

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem step_kill : G.AnnihilationProp := by
  intro hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 hPJ V _ _ π r hr x hx y hfix hj
  exact P_kill.core G π r (hPJ hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 V π r hr) x hx y hfix hj

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamBasic
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_triv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1 := by
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hker : (μ.ker : Set kˣ) ∈ nhds (1 : kˣ) := hμ.mem_nhds (one_mem _)
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hker
  obtain ⟨U, hU, hUsub⟩ := hker
  rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at hU
  obtain ⟨γ, hγ⟩ := hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hϖ1 : valuation k (ϖ : k) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hϖ.not_isUnit
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hϖ1 γ
  refine ⟨c, fun u hu => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨z, hz⟩ := hu
  have hz1 : valuation k (z : k) ≤ 1 := (Valuation.mem_integer_iff _ _).mp z.2
  have hv : valuation k (((unitIncl k u : kˣ) : k) - 1) < γ := by
    have h1 : ((unitIncl k u : kˣ) : k) - 1 = (ϖ : k) ^ c * (z : k) := by
      change ((u : 𝒪[k]) : k) - 1 = _
      have := congrArg (fun x : 𝒪[k] => (x : k)) hz
      push_cast at this
      exact this
    rw [h1, map_mul, map_pow]
    calc valuation k (ϖ : k) ^ c * valuation k (z : k) ≤ valuation k (ϖ : k) ^ c * 1 := by gcongr
      _ = valuation k (ϖ : k) ^ c := mul_one _
      _ < γ := hc
  exact hUsub (hγ hv)

theorem triv_cond (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (u : 𝒪[k]ˣ)
    (hu : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res μ)) : res μ u = 1 := by
  obtain ⟨c, hc⟩ := exists_triv μ hμ
  exact Nat.sInf_mem (s := {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1})
    ⟨c, hc⟩ u hu

theorem minor_unit {n r : ℕ} (hr : 1 ≤ r) {g : GL (Fin n) k} (hg : g ∈ KC k n r) {ι : Type} {_ : Fintype ι}
    {_ : DecidableEq ι} (f : ι → Fin n) (hf : Function.Injective f) :
    ∃ u : 𝒪[k]ˣ, ((g : Matrix (Fin n) (Fin n) k).submatrix f f).det = algebraMap 𝒪[k] k u ∧
      (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  obtain ⟨⟨h, rfl⟩, hc⟩ := hg
  set I := IsLocalRing.maximalIdeal 𝒪[k] ^ r
  set M : Matrix ι ι 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix f f with hM
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hentry : ∀ i j, (M i j) - (if i = j then 1 else 0) ∈ I := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hc (f i) (f j)
    have : y = M i j - (if i = j then 1 else 0) := by
      apply hinj
      rw [hyx]
      simp only [hM, Matrix.submatrix_apply, map_sub, hf.eq_iff]
      split_ifs <;> simp [Matrix.GeneralLinearGroup.map]
    rw [← this]
    exact hy
  have hmk : M.map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply]
    have := Ideal.Quotient.eq.mpr (hentry i j)
    rw [this]
    split_ifs <;> simp
  have hD : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.mapMatrix_apply, hmk, Matrix.det_one, map_one]
  have hDm : M.det - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := Ideal.pow_le_self (by omega) hD
  have hunit : IsUnit M.det := by
    by_contra hn
    have h1 : M.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 hDm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, RingHom.map_det]
    rfl
  · rw [IsUnit.unit_spec]
    exact hD

theorem chk_unit (μ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) : chk μ (algebraMap 𝒪[k] k u) = ((res μ u : ℂˣ) : ℂ) := by
  have h0 : algebraMap 𝒪[k] k u ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.val_injective (by simpa using h))
  rw [chk, dite_eq_right h0, show Units.mk0 _ h0 = unitIncl k u from Units.ext rfl]
  rfl

end UpperTheory.TNZ.Grp.P_lamBasic

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamBasic {n : ℕ} (G : Grp k n) : LambdaBasicProp G := by
  intro hb
  obtain ⟨-, hlt, hcond, hq⟩ := hb
  have hlev : 1 ≤ G.lev := by unfold lev; omega
  have key : ∀ g ∈ KC k n G.lev, G.lam g = 1 := by
    intro g hg
    unfold lam
    refine Finset.prod_eq_one fun a _ => ?_
    obtain ⟨u, hu, hu1⟩ := minor_unit hlev hg (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n)
      Subtype.val_injective
    have hΔ : G.Δ a g = algebraMap 𝒪[k] k u := hu
    rw [hΔ, chk_unit]
    unfold μnext
    split_ifs with h
    · have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h⟩ :=
        Ideal.pow_le_pow_right (hlt a _).le
      rw [hq a ⟨a + 1, h⟩ u (hle hu1)]
      rfl
    · rw [div_one]
      have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res (G.μ a)) :=
        Ideal.pow_le_pow_right (hcond a).le
      rw [triv_cond (G.μ a) (G.smooth a) u (hle hu1)]
      rfl
  have hone : (1 : GL (Fin n) k) ∈ KC k n G.lev := by
    refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
    simp [Matrix.one_apply]
  refine ⟨key 1 hone, fun g => ?_, key⟩
  unfold lam
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  unfold chk
  split_ifs
  · exact one_ne_zero
  · exact Units.ne_zero _

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamMul
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_lamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chk_mul (ψ : kˣ →* ℂˣ) {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    chk ψ (x * y) = chk ψ x * chk ψ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  unfold chk
  rw [dite_eq_right hxy, dite_eq_right hx, dite_eq_right hy]
  have e : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
  rw [e, map_mul, Units.val_mul]

theorem algebraMap_unit_ne_zero (u : 𝒪[k]ˣ) : algebraMap 𝒪[k] k (u : 𝒪[k]) ≠ 0 :=
  (u.isUnit.map (algebraMap 𝒪[k] k)).ne_zero

theorem chk_unit (ψ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) :
    chk ψ (algebraMap 𝒪[k] k (u : 𝒪[k])) = ((res ψ u : ℂˣ) : ℂ) := by
  unfold chk
  rw [dite_eq_right (algebraMap_unit_ne_zero u)]
  have e : Units.mk0 (algebraMap 𝒪[k] k (u : 𝒪[k])) (algebraMap_unit_ne_zero u) = unitIncl k u :=
    Units.ext rfl
  rw [e]
  rfl

variable {n : ℕ} (G : Grp k n)

theorem Δ_ne_zero (hU : ModulusOnUnitsProp G) (hB : CompactConductorBoundProp G) {g : GL (Fin n) k} (hg : g ∈ G.JSet)
    (a : Fin G.s) : G.Δ a g ≠ 0 := by
  obtain ⟨u, hu⟩ := hU hB g hg a
  rw [hu]
  exact algebraMap_unit_ne_zero u

theorem Δ_last (a : Fin G.s) (ha : ¬ (a : ℕ) + 1 < G.s) (g : GL (Fin n) k) :
    G.Δ a g = (g : Matrix (Fin n) (Fin n) k).det := by
  have hall : ∀ i : Fin n, G.bl i ≤ a := by
    intro i
    have := (G.bl i).isLt
    rw [Fin.le_def]
    omega
  unfold Δ
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv hall) _

theorem factor_mul (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) (a : Fin G.s) :
    chk (G.μ a / G.μnext a) (G.Δ a (g * h)) =
      chk (G.μ a / G.μnext a) (G.Δ a g) * chk (G.μ a / G.μnext a) (G.Δ a h) := by
  have hgz := Δ_ne_zero G hU hB hg a
  have hhz := Δ_ne_zero G hU hB hh a
  by_cases ha : (a : ℕ) + 1 < G.s
  · obtain ⟨u, hu1, hu⟩ := hM hC hB g hg h hh a ha
    have hn : G.μnext a = G.μ ⟨a + 1, ha⟩ := by unfold μnext; rw [dite_eq_left ha]
    have hres : ((res (G.μ a / G.μnext a) u : ℂˣ) : ℂ) = 1 := by
      rw [hn, hB.2.2.2 a ⟨a + 1, ha⟩ u hu1, Units.val_one]
    rw [hu, chk_mul _ (mul_ne_zero hgz hhz) (algebraMap_unit_ne_zero u), chk_unit, hres, mul_one,
      chk_mul _ hgz hhz]
  · rw [Δ_last G a ha, Δ_last G a ha, Δ_last G a ha, Units.val_mul, Matrix.det_mul]
    rw [← Δ_last G a ha g, ← Δ_last G a ha h]
    exact chk_mul _ hgz hhz

theorem lam_mul_of (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) : G.lam (g * h) = G.lam g * G.lam h := by
  unfold lam
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => factor_mul G hC hU hM hB hg hh a

end P_lamMul

theorem step_lamMul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : LambdaMultiplicativeProp G := by
  intro hC hU hM hB g hg h hh
  exact P_lamMul.lam_mul_of G hC hU hM hB hg hh

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamUnip
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamUnip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_eq_one_of_blockTri {ι β : Type} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (M : Matrix ι ι k) (b : ι → β) (hT : M.BlockTriangular b)
    (hD : ∀ i j, b i = b j → M i j = if i = j then 1 else 0) : M.det = 1 := by
  rw [hT.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have h1 : M.toSquareBlock b c = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    change M i j = (1 : Matrix {a' // b a' = c} {a' // b a' = c} k) ⟨i, hi⟩ ⟨j, hj⟩
    rw [Matrix.one_apply, hD i j (hi.trans hj.symm)]
    simp [Subtype.ext_iff]
  rw [h1, det_one]

theorem delta_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0)
    (a : Fin G.s) : G.Δ a g = 1 := by
  unfold Grp.Δ
  refine det_eq_one_of_blockTri _ (fun i : {i : Fin n // G.bl i ≤ a} => b (G.bl i.1)) ?_ ?_
  · intro i j h
    exact hT i.1 j.1 h
  · intro i j h
    change (g : Matrix (Fin n) (Fin n) k) i.1 j.1 = _
    rw [hD i.1 j.1 h]
    simp [Subtype.ext_iff]

theorem chk_one (μ : kˣ →* ℂˣ) : Grp.chk μ (1 : k) = 1 := by
  unfold Grp.chk
  rw [dite_eq_right one_ne_zero]
  have h : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
  rw [h, map_one, Units.val_one]

theorem lam_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) :
    G.lam g = 1 := by
  unfold Grp.lam
  refine Finset.prod_eq_one fun a _ => ?_
  rw [delta_eq_one G g b hT hD a, chk_one]

theorem diag_of_unipRad {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (hg : g ∈ unipRad k G.e) :
    ∀ i j, G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  have hD := (mem_unipRad.1 hg).2
  intro i j h
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  have hab : a = b := by simpa [Grp.bl] using h
  subst hab
  rw [hD a i' j', Matrix.one_apply]
  by_cases hij : i' = j'
  · subst hij; simp
  · rw [if_neg hij, if_neg]
    intro he
    have := G.e.injective he
    simp at this
    exact hij this

end UpperTheory.TNZ.Grp.P_lamUnip

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamUnip {n : ℕ} (G : Grp k n) : G.LambdaUnipotentProp := by
  refine ⟨fun u hu => ?_, fun u hu _ => ?_⟩
  · obtain ⟨hN, hK⟩ := Subgroup.mem_inf.1 hu
    have hP := (mem_unipRad.1 hN).1
    have hT : ∀ i j, G.bl j < G.bl i → ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 :=
      fun i j h => mem_parab.1 hP i j h
    refine ⟨⟨hK, fun i j hij => ?_⟩, P_lamUnip.lam_eq_one G u (fun a => a) hT
      (P_lamUnip.diag_of_unipRad G u hN)⟩
    rw [hT i j hij]
    exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · exact P_lamUnip.lam_eq_one G u (fun a => OrderDual.toDual a) (fun i j h => (hu i j).1 h)
      (fun i j h => (hu i j).2 h)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ.P_prodRc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem wd_eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero (h := h) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem main {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : Laws a ha ε rc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b))
      (hs : ∀ b, IsSmooth (σ b)) (hi : ∀ b, (σ b).IsIrreducible)
      (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b))) := by
  intro s
  induction s with
  | zero =>
    intro N d hd X _ _ σ hs hi hI
    have h0 : N = 0 := by simpa using hd.symm
    rw [List.ofFn_zero, sumList, List.foldr_nil]
    exact wd_eq_lpZero ((L.dim (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI)).trans h0)
  | succ s ih =>
    intro N d hd X _ _ σ hs hi hI
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨Φ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hts : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => σ i.succ) :=
      isSmooth_parInd _ _
    have hti := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0) _ (multiProd (stdBlocks d hd) σ)
      (hs 0) (hi 0) hts hI ⟨Φ.symm⟩
    have key := L.prod (d 0) (∑ i : Fin s, d i.succ) ⟨X 0, σ 0, hs 0, hi 0⟩ ⟨_, _, hts, hti⟩
      ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, hI⟩ ⟨Φ.symm⟩
    refine key.trans ?_
    rw [List.ofFn_succ, sumList, List.foldr_cons]
    congr 1
    exact ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs i.succ)
      (fun i => hi i.succ) hti

end UpperTheory.TNZ.P_prodRc

namespace UpperTheory.TNZ

theorem step_prodRc : ProductRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc L s N d hd X _ _ σ hs hi hI
  exact P_prodRc.main L s N d hd X σ hs hi hI

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Uniformizer₂
section
noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
end
end

