module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt
section
noncomputable section

namespace LocMassOrdLat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain Topology Matrix Filter
open scoped TensorProduct

attribute [local instance] LocMassOrdSF.finDim_FE LocMassOrdSF.isModTop_tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section OEvOpen

variable (v : HeightOneSpectrum (𝓞 F))

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

def Osub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  add_mem' := oev_add v
  zero_mem' := oev_zero v
  neg_mem' := oev_neg v

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E,
    ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b0)
  have hu : ∀ i : Fin (Module.finrank F E), IsUnit ((y : F)) := fun _ =>
    isUnit_iff_ne_zero.2 (by exact_mod_cast hy0)
  refine ⟨b0.isUnitSMul hu, fun i => ?_⟩
  have h := hy (b0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [Module.Basis.isUnitSMul_apply]
  have e : ((y : F)) • b0 i = y • b0 i := by
    rw [← Int.cast_smul_eq_zsmul F y (b0 i)]
  rw [e]
  exact h

def ib : Module.Basis (Fin (Module.finrank F E)) F E := (exists_intBasis (F := F) (E := E)).choose

theorem ib_int (i : Fin (Module.finrank F E)) : IsIntegral ℤ (ib (F := F) (E := E) i) :=
  (exists_intBasis (F := F) (E := E)).choose_spec i

def bas : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (ib (F := F) (E := E))

theorem bas_apply (i : Fin (Module.finrank F E)) :
    bas (E := E) v i = inclR (F := F) (Fv F v) (ib (F := F) (E := E) i) := by
  simp [bas, Algebra.TensorProduct.basis_apply, inclR]

theorem bas_mem (i : Fin (Module.finrank F E)) : bas (E := E) v i ∈ OEv (E := E) v := by
  rw [bas_apply]
  exact LocMassOrdKv.inclR_mem v ⟨_, ib_int i⟩

theorem oev_mem_nhds : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  set e := (bas (E := E) v).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ho : IsOpen (e ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  refine Filter.mem_of_superset (ho.mem_nhds (by simp [zero_mem])) ?_
  intro x hx
  rw [← (bas (E := E) v).sum_equivFun x]
  exact Submodule.sum_mem _ fun i _ => LocMassOrdKv.oev_smul v (hx i trivial) (bas_mem v i)

theorem isOpen_oev : IsOpen (OEv (E := E) v) :=
  AddSubgroup.isOpen_of_mem_nhds (Osub (E := E) v) (oev_mem_nhds v)

end OEvOpen

section NotDiscrete

variable (v : HeightOneSpectrum (𝓞 F))

theorem exists_ne_zero_mem_nhds {U : Set (Fv F v)} (hU : U ∈ 𝓝 (0 : Fv F v)) :
    ∃ t ∈ U, t ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 : ({0} : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) := Filter.mem_of_superset hU fun t ht => h t ht
  have hop : IsOpen ({0} : Set (Fv F v)) := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    rw [Set.mem_singleton_iff.mp hx]
    exact h0
  have : DiscreteTopology (Fv F v) := discreteTopology_of_isOpen_singleton_zero hop
  have hfin : (v.adicCompletionIntegers F : Set (Fv F v)).Finite :=
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).finite_of_discrete
  have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : (v.adicCompletionIntegers F : Set (Fv F v)).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : Fv F v)) Nat.cast_injective
      fun k => natCast_mem _ k
  exact hinf hfin

theorem exists_scale {ι : Type} [Finite ι] {W : Type} [AddCommGroup W] [Module (Fv F v) W]
    [TopologicalSpace W] [ContinuousSMul (Fv F v) W] {L : Set W} (hL : L ∈ 𝓝 (0 : W))
    (e : ι → W) : ∃ t : Fv F v, t ≠ 0 ∧ ∀ i, t • e i ∈ L := by
  have hi : ∀ i, (fun t : Fv F v => t • e i) ⁻¹' L ∈ 𝓝 (0 : Fv F v) := by
    intro i
    refine (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa using hL
  have hU : (⋂ i, (fun t : Fv F v => t • e i) ⁻¹' L) ∈ 𝓝 (0 : Fv F v) := Filter.iInter_mem.mpr hi
  obtain ⟨t, ht, ht0⟩ := exists_ne_zero_mem_nhds v hU
  exact ⟨t, ht0, fun i => Set.mem_iInter.mp ht i⟩

end NotDiscrete

section Lat

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_smul (c : Fv F v) (w : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • w) = c • sigR (Fv F v) σ w := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, Finset.smul_sum]

theorem hR_mem_of_gens (Λ : Set (Fin n → E)) {m : ℕ} (g : Fin m → Fin n → Fv F v ⊗[F] E)
    (hg : Submodule.span (v.adicCompletionIntegers F) (Set.range g) = latLoc (E := E) v Λ)
    (y : Fin n → Fv F v ⊗[F] E) (hy : ∀ a, hR (Fv F v) σ J (g a) y ∈ OEv (E := E) v) :
    ∀ x ∈ latLoc (E := E) v Λ, hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  intro x hx
  rw [← hg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hy a
  | zero =>
    rw [hR_zero_left]
    exact oev_zero v
  | add x x' _ _ h1 h2 =>
    rw [hR_add_left]
    exact oev_add v h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, hR_smul_left]
    exact LocMassOrdKv.oev_smul v c.2 h

theorem gens_mem (Λ : Set (Fin n → E)) {m : ℕ} (g : Fin m → Fin n → Fv F v ⊗[F] E)
    (hg : Submodule.span (v.adicCompletionIntegers F) (Set.range g) = latLoc (E := E) v Λ)
    (a : Fin m) : g a ∈ latLoc (E := E) v Λ := by
  rw [← hg]
  exact Submodule.subset_span ⟨a, rfl⟩

theorem isOpen_latLoc (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ)
    (hFG : (latLoc (E := E) v Λ).FG) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hFG
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      ⋂ a, (fun y => hR (Fv F v) σ J (g a) y) ⁻¹' OEv (E := E) v := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hy a
      exact (hSD y).mp hy (g a) (gens_mem v Λ g hg a)
    · intro hy
      exact (hSD y).mpr (hR_mem_of_gens σ J v Λ g hg y hy)
  rw [e]
  exact isOpen_iInter_of_finite fun a =>
    (isOpen_oev v).preimage (LocMassOrdKv.continuous_hR_right σ J v (g a))

theorem isCompact_latLoc (Λ : Set (Fin n → E)) (hFG : (latLoc (E := E) v Λ).FG) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hFG
  have hK : IsCompact (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hcont : Continuous fun c : Fin m → Fv F v => ∑ k, c k • g k :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      (fun c : Fin m → Fv F v => ∑ k, c k • g k) ''
        (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro h
      rw [SetLike.mem_coe, ← hg] at h
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
      exact ⟨fun k => (c k : Fv F v), fun k _ => (c k).2, hc⟩
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, ← hg]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ (⟨c k, hc k trivial⟩ : v.adicCompletionIntegers F)
          (Submodule.subset_span ⟨k, rfl⟩)
  rw [e]
  exact hK.image hcont

end Lat

end LocMassOrdLat
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.MeasurableConjugateCompact
section
noncomputable section

namespace LocMassOrdSC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain LocMassOrdW
open scoped TensorProduct Classical

def MeasUO : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r : ℕ), MeasurableSet (UO (E := E) v r)

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem kvc_mul {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).mul_mem ha hb

theorem kvc_inv {a : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    a⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).inv_mem ha

theorem kvc_mem_lat {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : z ∈ latLoc (E := E) v Λ) :
    lin (Fv F v) σ J k z ∈ latLoc (E := E) v Λ :=
  (hk z).1 hz

theorem sc_mul (a b : Fv F v) : sc (E := E) v a * sc (E := E) v b = sc (E := E) v (a * b) := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem dV_ne : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne v))
  · exact one_ne_zero

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))

theorem uo_of_mem {y : HA (Fv F v) σ J}
    (hy : IsPrim v Λ (locF v (y • ratTup (Fv F v) (F0 P))))
    (s0 : S0 (Fv F v) σ J P) (g : HA (Fv F v) σ J) (x : UIdx r → Fv F v ⊗[F] E)
    (hg : ∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a))
    (hk : y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    x ∈ UO (E := E) v r := by
  set X : TupV (E := E) v n (r + 1) := y • ratTup (Fv F v) (F0 P) with hX
  have hXa : ∀ a, X a = lin (Fv F v) σ J y (ratV (F := F) (Fv F v) (F0 P a)) := fun a => rfl
  have hs0 : ∀ a, lin (Fv F v) σ J (s0 : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P a)) =
      ratV (F := F) (Fv F v) (F0 P a) := fun a =>
    congrFun (s0.2 : (s0 : HA (Fv F v) σ J) • ratTup (Fv F v) (F0 P) = ratTup (Fv F v) (F0 P)) a
  have hkX : ∀ b, lin (Fv F v) σ J (y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹) (X b) =
      ∑ a, uMat v x a b • X a := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hXa, lin_mul, lin_inv_lin, lin_mul, lin_mul, hg, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hs0, map_smul, hXa]
  intro p
  obtain ⟨⟨a, b⟩, hab⟩ := p
  let c : Fin (r + 1) → Fv F v ⊗[F] E := fun a =>
    sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v x a b
  have key : ∑ a, c a • locF v X a =
      lin (Fv F v) σ J (y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹) (locF v X b) := by
    simp only [locF, map_smul, hkX, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    have e1 : sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * sc (E := E) v (alp v r a) =
        sc (E := E) v (alp v r b) := by
      rw [sc_mul]
      congr 1
      field_simp [alp_ne v r a]
    calc c a * sc (E := E) v (alp v r a)
        = uMat v x a b * (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) *
            sc (E := E) v (alp v r a)) := by simp only [c]; ring
      _ = sc (E := E) v (alp v r b) * uMat v x a b := by rw [e1, mul_comm]
  have hmem : ∑ a, c a • locF v X a ∈ latLoc (E := E) v Λ := by
    rw [key]
    exact kvc_mem_lat σ J v Λ hk (hy.1 b)
  have := hy.2 c hmem a
  simp only [c, uMat, if_neg hab.ne, dif_pos hab] at this
  exact this

end Main

theorem stepC_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J)
    (h : FrameHyp σ J ψ v P Λ μG μS μS0 y)
    (hC0 : MeasurableSet {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v})
    (hU0 : MeasurableSet (UO (E := E) v r))
    (hE0 : ∀ x : UIdx r → Fv F v ⊗[F] E, ∃ g : HA (Fv F v) σ J,
      ∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a))
    (hK0 : ∀ x ∈ UO (E := E) v r, ∃ g : HA (Fv F v) σ J,
      (∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)) ∧
      y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    μS (KSvT σ J v P Λ y) = μS0 (stabilizerConjugateCompact σ J v P Λ y) * sdE (E := E) ψ v (UIdx r) (UO v r) := by
  obtain ⟨_, _, _, _, _, _, _, _, hpu, hy⟩ := id h
  have hC := hC0
  set C := {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v} with hCdef
  let t : (UIdx r → Fv F v ⊗[F] E) → HA (Fv F v) σ J := fun x =>
    if hx : x ∈ UO (E := E) v r then (hK0 x hx).choose
    else (hE0 x).choose
  have ht : ∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a) := by
    intro x b
    by_cases hx : x ∈ UO (E := E) v r
    · simp only [t, dif_pos hx]
      exact (hK0 x hx).choose_spec.1 b
    · simp only [t, dif_neg hx]
      exact (hE0 x).choose_spec b
  have htK : ∀ x ∈ UO (E := E) v r, y * t x * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    intro x hx
    simp only [t, dif_pos hx]
    exact (hK0 x hx).choose_spec.2
  have hiff : ∀ x (s0 : S0 (Fv F v) σ J P), (s0 : HA (Fv F v) σ J) * t x ∈ C ↔
      x ∈ UO (E := E) v r ∧ s0 ∈ stabilizerConjugateCompact σ J v P Λ y := by
    intro x s0
    constructor
    · intro hk
      have hx := uo_of_mem σ J v P Λ hy s0 (t x) x (ht x) hk
      refine ⟨hx, ?_⟩
      have := kvc_mul σ J v Λ hk (kvc_inv σ J v Λ (htK x hx))
      change y * (s0 : HA (Fv F v) σ J) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v
      convert this using 1
      group
    · rintro ⟨hx, hs⟩
      have := kvc_mul σ J v Λ hs (htK x hx)
      rw [hCdef, Set.mem_ofPred_eq]
      convert this using 1
      group
  have hL : μS (KSvT σ J v P Λ y) = ∫⁻ g, C.indicator 1 g ∂(amb μS) := by
    rw [lintegral_indicator_one hC, Measure.map_apply measurable_subtype_coe hC]
    rfl
  rw [hL, hpu (C.indicator 1) (measurable_one.indicator hC) t ht]
  have hs0m : MeasurableSet (stabilizerConjugateCompact σ J v P Λ y) := measurable_subtype_coe hC
  have hpt : ∀ x, ∫⁻ s0, C.indicator 1 ((s0 : HA (Fv F v) σ J) * t x) ∂μS0 =
      (UO (E := E) v r).indicator 1 x * μS0 (stabilizerConjugateCompact σ J v P Λ y) := by
    intro x
    have hq : ∀ s0 : S0 (Fv F v) σ J P,
        C.indicator (1 : HA (Fv F v) σ J → ENNReal) ((s0 : HA (Fv F v) σ J) * t x) =
          (UO (E := E) v r).indicator 1 x * (stabilizerConjugateCompact σ J v P Λ y).indicator 1 s0 := by
      intro s0
      by_cases h1 : (s0 : HA (Fv F v) σ J) * t x ∈ C
      · obtain ⟨a1, a2⟩ := (hiff x s0).1 h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem a1, Set.indicator_of_mem a2]
        simp
      · rw [Set.indicator_of_notMem h1]
        by_cases a1 : x ∈ UO (E := E) v r
        · have a2 : s0 ∉ stabilizerConjugateCompact σ J v P Λ y := fun a2 => h1 ((hiff x s0).2 ⟨a1, a2⟩)
          rw [Set.indicator_of_notMem a2, mul_zero]
        · rw [Set.indicator_of_notMem a1, zero_mul]
    simp_rw [hq]
    rw [lintegral_const_mul _ (measurable_one.indicator hs0m), lintegral_indicator_one hs0m]
  simp_rw [hpt]
  rw [lintegral_mul_const _ (measurable_one.indicator hU0), lintegral_indicator_one hU0,
    mul_comm]

theorem measConj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ) (y : HA (Fv F v) σ J) :
    MeasurableSet {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v} := by
  have hc : Continuous fun g : HA (Fv F v) σ J => y * g * y⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact hc.measurable (LocMassOrdKv.kv_measurableSet σ J v Λ hSD)

theorem measurable_unipotent_orbit : MeasUO := by
  intro F E _ _ _ _ _ v r
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hset : UO (E := E) v r = ⋂ p : UIdx r, (fun x : UIdx r → Fv F v ⊗[F] E => x p) ⁻¹'
      ((fun z : Fv F v ⊗[F] E => sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * z) ⁻¹'
        OEv (E := E) v) := by
    ext x
    simp [UO]
  rw [hset]
  refine MeasurableSet.iInter fun p => measurable_pi_apply p ?_
  exact ((LocMassOrdKv.isClosed_oev v).preimage
    (continuous_const.mul continuous_id)).measurableSet

end LocMassOrdSC
end
end

