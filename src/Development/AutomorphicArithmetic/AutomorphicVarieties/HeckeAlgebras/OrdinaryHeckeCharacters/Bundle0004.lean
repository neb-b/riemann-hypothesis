module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClFinMulVec
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem clFin_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
    (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
  simp only [mulVec, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨x, hx⟩ := hM k j
  rw [← hx, ← Algebra.smul_def]
  exact L.smul_mem x (hv j)

private theorem clFin_key {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (hτ : ∀ u i j, (τ u).val i j ∈ (algebraMap O Ω).range) (φ : X.I.T →* Ωˣ) (c : ℕ)
    (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) (U : Subgroup X.Ub) (hU : X.FinLevel U) :
    ∃ S : Finset (Ga × Gp), ∀ F ∈ X.Cl τ W.ξ U c φ, ∀ L : Submodule O Ω,
      (∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k ∈ L) → ∀ g i k, (((W.ξ g.2)⁻¹).val *ᵥ F i g) k ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).2
  haveI := Fintype.ofFinite (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0))
  refine ⟨(s ×ˢ (Finset.univ : Finset (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)))).image
    (fun p => p.1 * (1, ((p.2.out : X.I.Iw 0) : Gp))), ?_⟩
  rintro F ⟨⟨hA, hU⟩, hN, hM, hT⟩ L hL g i
  obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
  obtain ⟨e, he⟩ := QuotientGroup.mk_out_eq_mul ((X.I.I1 c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
  have he1 : ((e : X.I.Iw 0) : Gp) ∈ X.I.I1 c := Subgroup.mem_subgroupOf.1 e.2
  set r : Gp := ((⟨b, hb⟩ : X.I.Iw 0) : X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)).out.1 with hr
  have hr2 : r = b * ((e : X.I.Iw 0) : Gp) := by rw [hr, he]; rfl
  have hL1 := hL (x * (1, r)) (Finset.mem_image.2 ⟨(x, _), Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩, rfl⟩)
  generalize ((e : X.I.Iw 0) : Gp) = e' at he1 hr2
  have hfix : ∀ w ∈ X.I.I1 c, X.rpF Ω (W.d + 1) m w F = F := by
    intro w hw
    obtain ⟨n, hn, t, ht, y, hy, rfl⟩ := (iwMem Gp X.I c w).2.1.1 hw
    have h3 := hT ⟨t, X.I.Tc_le c ht⟩
    rw [hφ _ ht, inv_one, Units.val_one, one_smul] at h3
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hM y hy, h3, hN n hn]
  have hint : ∀ v : Fin (W.d + 1) → Ω, (∀ k, v k ∈ L) → ∀ k, ((W.ξ e').val *ᵥ v) k ∈ L := by
    intro v hv
    obtain ⟨n, hn, t, ht, y, hy, rfl⟩ := (iwMem Gp X.I c _).2.1.1 he1
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact clFin_mulVec L _ (W.int_N n hn) _ (clFin_mulVec L _ (W.integral_torusCharacter t (X.I.Tc_le c ht)) _
      (clFin_mulVec L _ (W.int_Nm y (X.I.Nm_anti hc hy)) _ hv))
  have e1 : X.glob γ * x * ((u : Ga), b) = X.glob γ * (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹)) := by
    rw [hr2]; simp [mul_assoc]
  have e2 : F i (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹)) = F i (x * (1, r) * ((u : Ga), 1)) :=
    congrFun (congrFun (hfix _ (inv_mem he1)) i) _
  have e3 : F i (x * (1, r) * ((u : Ga), 1)) = ∑ j, (τ u⁻¹).val i j • F j (x * (1, r)) := by
    funext k
    have := congrFun (congrFun (congrFun (hU u⁻¹ (inv_mem hu)) i) (x * (1, r) * ((u : Ga), 1))) k
    rw [← this]
    change ((τ u⁻¹).val *ᵥ fun j => F j (x * (1, r) * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), 1)) k) i = _
    simp [mulVec, dotProduct, mul_assoc, ← Prod.one_eq_mk]
  have e4 : ((W.ξ (X.glob γ * (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹))).2)⁻¹).val * (W.ξ (X.glob γ).2).val
      = (W.ξ e').val * ((W.ξ (x * (1, r)).2)⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp [mul_assoc]
  rw [e1, hA i trivial γ, mulVec_mulVec, e4, ← mulVec_mulVec, e2, e3]
  refine hint _ fun k => ?_
  rw [mulVec_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, ha⟩ := hτ u⁻¹ i j
  rw [mulVec_smul, ← ha, Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  exact L.smul_mem a (hL1 j k)

private theorem clFin_zero {Ω : Type} [Field Ω] {n : ℕ} (M : GL (Fin n) Ω) (v : Fin n → Ω)
    (h : (M⁻¹).val *ᵥ v = 0) : v = 0 := by
  have := congrArg (M.val *ᵥ ·) h
  simpa [mulVec_mulVec] using this

theorem UpperTheory.V.Hi.clFin :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) →
      ∀ (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ) (c : ℕ), W.c0 ≤ c →
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) →
      ∀ U : Subgroup X.Ub, X.FinLevel U → X.Free τ θ U → FiniteDimensional Ω (X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)) ∧ ∀ a : X.I.P, (∀ F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), X.UF m W a F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)) ∧ ∀ F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), F ≠ 0 → ∀ μ : Ω, X.UF m W a F = μ • F → IsIntegral O μ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ _ _ _ W m τ θ φ c hc hφ _ U hU _
  classical
  have hτ : ∀ u i j, (((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u).val i j ∈ (algebraMap O Ω).range :=
    fun u i j => ⟨(τ u).val i j, rfl⟩
  have hφ' : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → ((Units.map (algebraMap O Ω).toMonoidHom).comp φ) t = 1 :=
    fun t ht => by rw [MonoidHom.comp_apply, hφ t ht, map_one]
  generalize (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ = τ' at hτ ⊢
  generalize (Units.map (algebraMap O Ω).toMonoidHom).comp φ = φ' at hφ' ⊢
  obtain ⟨S, hS⟩ := clFin_key X W τ' hτ φ' c hc hφ' U hU
  have hz : ∀ F ∈ X.Cl τ' W.ξ U c φ', (∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k = 0) → F = 0 := by
    intro F hF h
    funext i g
    exact clFin_zero (W.ξ g.2) _ (funext fun k => hS F hF ⊥ h g i k)
  refine ⟨?_, fun a => ?_⟩
  · let ev : X.Cl τ' W.ξ U c φ' →ₗ[Ω] (S → Fin m → Fin (W.d + 1) → Ω) :=
      { toFun := fun F x i => F.1 i x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun F h => Subtype.ext ?_)
    refine hz F.1 F.2 fun x hx i k => ?_
    have : F.1 i x = 0 := congrFun (congrFun h ⟨x, hx⟩) i
    rw [this, mulVec_zero]; rfl
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) a a.2
  have hsum : ∀ F ∈ X.Cl τ' W.ξ U c φ', X.UF m W a F =
      (((W.χ ⟨a, X.I.P_le a a.2⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * a) F := by
    intro F hF
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨fun F hF => ⟨?_, ?_⟩, fun F hF h0 μ hμ => ?_⟩
  · rw [hsum F hF]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * a)) = _ *ᵥ F i (g * (1, u * a))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · funext i g k
      have := congrFun (congrFun (congrFun (hF.1.2 w hw) i) (g * (1, u * a))) k
      refine Eq.trans ?_ this
      change ((τ' w).val *ᵥ fun j => F j (g * ((w : Ga), 1) * (1, u * a)) k) i =
        ((τ' w).val *ᵥ fun j => F j (g * (1, u * a) * ((w : Ga), 1)) k) i
      simp [mul_assoc]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ' hφ').1 a a.2 F hF.2)
  let L : Submodule O Ω := Submodule.span O (Set.range
    fun p : S × Fin m × Fin (W.d + 1) => (((W.ξ p.1.1.2)⁻¹).val *ᵥ F p.2.1 p.1.1) p.2.2)
  have hL0 : ∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k ∈ L :=
    fun x hx i k => Submodule.subset_span ⟨(⟨x, hx⟩, i, k), rfl⟩
  have hL := hS F hF L hL0
  have hμL : ∀ g i k, μ * (((W.ξ g.2)⁻¹).val *ᵥ F i g) k ∈ L := by
    intro g i k
    have e : μ • F i g = (((W.χ ⟨a, X.I.P_le a a.2⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, F i (g * (1, u * a)) := by
      have := congrFun (congrFun (hμ.symm.trans (hsum F hF)) i) g
      simp only [Pi.smul_apply, Finset.sum_apply] at this
      exact this
    rw [← smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul, e, Finset.smul_sum, mulVec_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ fun u hu => ?_
    have e4 : ((W.ξ g.2)⁻¹).val = (W.ξ u).val * ((W.ξ a).val * ((W.ξ (g * (1, u * a)).2)⁻¹).val) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      simp [mul_assoc]
    rw [e4, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, mulVec_smul, ← smul_mulVec]
    exact clFin_mulVec L _ (W.int_N u (hs u hu)) _ (clFin_mulVec L _ (W.int_P a a.2) _ (hL _ i)) k
  refine isIntegral_of_smul_mem_submodule L (fun h => h0 (hz F hF fun x hx i k => ?_))
    (Submodule.fg_span (Set.finite_range _)) μ fun n hn => ?_
  · have := hL0 x hx i k
    rwa [h] at this
  · induction hn using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact hμL _ _ _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_comm]; exact L.smul_mem r hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem spStab_per {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (V : Submodule A M)
    (T : Module.End A M) (hT : ∀ v ∈ V, T v ∈ V) (f : M) :
    f ∈ (⨆ n : ℕ, V.comap (T ^ (n + 1) - 1)) ↔ ∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V := by
  have hp : ∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V := by
    intro n v hv
    induction n with
    | zero => simpa using hv
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
  have hm : ∀ (n j : ℕ) (v : M), (T ^ n) v - v ∈ V → (T ^ (n * j)) v - v ∈ V := by
    intro n j v hv
    induction j with
    | zero => simp
    | succ j ih =>
      have := add_mem (hp n _ ih) hv
      rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
      convert this using 1
      rw [map_sub]
      abel
  rw [Submodule.mem_iSup_of_directed]
  · simp
  · intro a b
    refine ⟨a * b + a + b, fun v hv => ?_, fun v hv => ?_⟩
    · have := hm (a + 1) (b + 1) v (by simpa using hv)
      rw [show (a + 1) * (b + 1) = a * b + a + b + 1 by ring] at this
      simpa using this
    · have := hm (b + 1) (a + 1) v (by simpa using hv)
      rw [show (b + 1) * (a + 1) = a * b + a + b + 1 by ring] at this
      simpa using this

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}

private theorem spStab_rp (b : Gp) (f : X.Fn A m) (g : Ga × Gp) : X.rp A m b f g = f (g * (1, b)) := rfl

private theorem spStab_U {a : Gp} (ha : a ∈ X.I.P) :
    ∃ (ι : Type) (s : Finset ι) (b : ι → Gp), ∀ f : X.Fn A m, X.U A m a f = ∑ i ∈ s, X.rp A m (b i) f := by
  haveI : ((X.I.Nconj a).subgroupOf X.I.N).FiniteIndex := ⟨X.I.fin_N a ha⟩
  haveI : Fintype (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N) := Fintype.ofFinite _
  refine ⟨X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N, Finset.univ, fun q => (q.out : X.I.N) * a, fun f => ?_⟩
  unfold Frame.U Iwa.uOp
  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private theorem spStab_comm (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) (f : X.Fn A m) :
    X.ra τ u (X.rp A m b f) = X.rp A m b (X.ra τ u f) := by
  funext g
  rw [Frame.ra_apply, spStab_rp, spStab_rp, Frame.ra_apply]
  simp [mul_assoc]

private theorem spStab_commU (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) {a : Gp} (ha : a ∈ X.I.P) (f : X.Fn A m) :
    X.ra τ u (X.U A m a f) = X.U A m a (X.ra τ u f) := by
  obtain ⟨ι, s, b, h⟩ := spStab_U X (A := A) (m := m) ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, h, map_sum]
  exact Finset.sum_congr rfl fun i _ => spStab_comm X τ u _ f

variable [IsLocalRing A]

private theorem spStab_val (k : ℕ) (f : X.Fn A m) : f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
  simp [Frame.valIn, Submodule.mem_pi]

private theorem spStab_valU (k : ℕ) {a : Gp} (ha : a ∈ X.I.P) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    X.U A m a f ∈ X.valIn A m k := by
  obtain ⟨ι, s, b, h⟩ := spStab_U X (A := A) (m := m) ha
  rw [h]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [spStab_val] at hf ⊢
  exact fun g j => hf _ j

private theorem spStab_valra (τ : X.Ub →* GL (Fin m) A) (k : ℕ) (u : X.Ub) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    X.ra τ u f ∈ X.valIn A m k := by
  rw [spStab_val] at hf ⊢
  intro g i
  rw [Frame.ra_apply]
  simp only [mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hf _ j)

private theorem spStab_ord (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (f : X.Fn A m) :
    f ∈ X.Ord τ θ U ↔ f ∈ X.Sp τ θ U ∧ ∀ k, ∃ n : ℕ, (X.U A m X.I.z ^ (n + 1)) f - f ∈ X.valIn A m k := by
  rw [Frame.Ord, Submodule.mem_inf, Submodule.mem_iInf]
  exact and_congr Iff.rfl (forall_congr' fun k => spStab_per _ _ (spStab_valU X k X.I.z_mem) f)

private theorem spStab_ambra (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (u : X.Ub) (f : X.Fn A m)
    (hf : f ∈ X.Amb m θ) : X.ra τ u f ∈ X.Amb m θ := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨fun γ g => by rw [Frame.ra_apply, Frame.ra_apply, mul_assoc, h1],
    fun x hx => by rw [← spStab_comm, h2 x hx], fun t => by rw [← spStab_comm, h3, map_smul], fun k => ?_⟩
  obtain ⟨c, hc⟩ := h4 k
  refine ⟨c, fun y hy => ?_⟩
  have : X.rp A m y f - f ∈ X.valIn A m k := (spStab_val X k _).2 (hc y hy)
  have h5 := spStab_valra X τ k u _ this
  rw [map_sub, spStab_comm] at h5
  exact (spStab_val X k _).1 h5

private theorem spStab_ambU (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) {a : Gp} (ha : a ∈ X.I.P) (f : X.Fn A m)
    (hf : f ∈ X.Amb m θ) : X.U A m a f ∈ X.Amb m θ := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  obtain ⟨e1, -, -, e2, -⟩ := uOpMul Gp X.I A _ (X.rp A m) a a ha ha f h2
  refine ⟨fun γ g => ?_, e1, fun t => ?_, fun k => ?_⟩
  · obtain ⟨ι, s, b, h⟩ := spStab_U X (A := A) (m := m) ha
    rw [h, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [spStab_rp, spStab_rp, mul_assoc, h1]
  · unfold Frame.U
    rw [e2 t t.2, h3, map_smul]
  · obtain ⟨c1, hc1⟩ := h4 k
    obtain ⟨c2, hc2⟩ := hθ k
    refine ⟨max c1 c2, fun y hy g i => ?_⟩
    let φ : X.Fn A m →ₗ[A] X.Fn (A ⧸ maximalIdeal A ^ k) m := X.mapFn
    have hφ : ∀ f g i, φ f g i = Ideal.Quotient.mk _ (f g i) := fun _ _ _ => rfl
    have hnat : ∀ b f, φ (X.rp A m b f) = X.rp _ m b (φ f) := fun _ _ => rfl
    have hfix : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.I1 (max c1 c2)) := by
      intro w hw
      obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem Gp X.I _ w).2.1.1 hw
      have a3 : X.rp _ m y (φ f) = φ f := by
        funext g i
        rw [spStab_rp, hφ, hφ, Ideal.Quotient.eq]
        exact hc1 y (X.I.Nm_anti (le_max_left _ _) hy) g i
      have a2 : X.rp _ m t (φ f) = φ f := by
        have ht' := X.I.Tc_le _ ht
        have := hc2 ⟨t, ht'⟩⁻¹ (inv_mem (X.I.Tc_anti (le_max_right _ _) ht))
        rw [← hnat, h3 ⟨t, ht'⟩]
        funext g i
        rw [hφ, hφ, Ideal.Quotient.eq]
        have h6 := Ideal.mul_mem_right (f g i) _ this
        rw [map_inv] at h6
        convert h6 using 1
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, a3, a2, ← hnat, h2 x hx]
    have h7 := (uOpLevel Gp X.I _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) (max c1 c2)).1 a ha _ hfix y
      (Subgroup.mem_sup_right hy)
    have h8 := uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) φ.toAddMonoidHom a ha f
      (fun _ _ => rfl)
    change φ _ = X.I.uOp _ a (φ f) at h8
    rw [← h8] at h7
    have h9 := congrFun (congrFun h7 g) i
    rw [spStab_rp, hφ, hφ, Ideal.Quotient.eq] at h9
    exact h9

end

theorem UpperTheory.V.Hi.spStab :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → (∀ a ∈ X.I.P, ∀ f ∈ X.Amb m θ, X.U A m a f ∈ X.Amb m θ) ∧ (∀ u, ∀ f ∈ X.Amb m θ, X.ra τ u f ∈ X.Amb m θ) ∧ (∀ a ∈ X.I.P, ∀ u f, X.ra τ u (X.U A m a f) = X.U A m a (X.ra τ u f)) ∧ (∀ U, ∀ a ∈ X.I.P, (∀ f ∈ X.Sp τ θ U, X.U A m a f ∈ X.Sp τ θ U) ∧ ∀ f ∈ X.Ord τ θ U, X.U A m a f ∈ X.Ord τ θ U) ∧ ∀ (U V K K' : Subgroup X.Ub) (x : X.Ub), (MulAction.orbit K (x : X.Ub ⧸ K')).Finite → (∀ f ∈ fixd (X.ra τ) V, dc (X.ra τ) K K' x f ∈ fixd (X.ra τ) U) → ∀ f ∈ X.Ord τ θ V, dc (X.ra τ) K K' x f ∈ X.Ord τ θ U := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ
  have hSp : ∀ U, ∀ a ∈ X.I.P, ∀ f ∈ X.Sp τ θ U, X.U A m a f ∈ X.Sp τ θ U := fun U a ha f hf =>
    ⟨spStab_ambU X θ hθ ha f hf.1, fun u hu => by rw [spStab_commU X τ u ha, hf.2 u hu]⟩
  refine ⟨fun a ha f hf => spStab_ambU X θ hθ ha f hf, fun u f hf => spStab_ambra X τ θ u f hf,
    fun a ha u f => spStab_commU X τ u ha f, fun U a ha => ⟨hSp U a ha, fun f hf => ?_⟩, ?_⟩
  · rw [spStab_ord] at hf ⊢
    refine ⟨hSp U a ha f hf.1, fun k => ?_⟩
    obtain ⟨n, hn⟩ := hf.2 k
    have hN : f ∈ fixd (X.rp A m) X.I.N := hf.1.1.2.1
    have key : ∀ j : ℕ, (X.U A m X.I.z ^ j) f ∈ fixd (X.rp A m) X.I.N ∧
        X.U A m a ((X.U A m X.I.z ^ j) f) = (X.U A m X.I.z ^ j) (X.U A m a f) := by
      intro j
      induction j with
      | zero => exact ⟨hN, rfl⟩
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih.2]
        have b1 := uOpMul Gp X.I A _ (X.rp A m) a X.I.z ha X.I.z_mem _ ih.1
        have b2 := uOpMul Gp X.I A _ (X.rp A m) X.I.z a X.I.z_mem ha _ ih.1
        refine ⟨b2.1, b1.2.1.trans (Eq.trans ?_ b2.2.1.symm)⟩
        rw [X.I.comm a (X.I.P_le a ha) X.I.z (X.I.P_le _ X.I.z_mem)]
    refine ⟨n, ?_⟩
    rw [← (key _).2, ← map_sub]
    exact spStab_valU X k ha _ hn
  · intro U V K K' x hfin hfix f hf
    letI : Fintype (MulAction.orbit K (x : X.Ub ⧸ K')) := hfin.fintype
    have hdc : ∀ v, dc (X.ra τ) K K' x v =
        ∑ q : MulAction.orbit K (x : X.Ub ⧸ K'), X.ra τ (q : X.Ub ⧸ K').out v := fun v => by
      rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    rw [spStab_ord] at hf ⊢
    refine ⟨⟨?_, hfix f hf.1.2⟩, fun k => ?_⟩
    · rw [hdc]
      exact Submodule.sum_mem _ fun q _ => spStab_ambra X τ θ _ f hf.1.1
    · obtain ⟨n, hn⟩ := hf.2 k
      have key : ∀ (u : X.Ub) (j : ℕ), X.ra τ u ((X.U A m X.I.z ^ j) f) = (X.U A m X.I.z ^ j) (X.ra τ u f) := by
        intro u j
        induction j with
        | zero => rfl
        | succ j ih =>
          rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, spStab_commU X τ u X.I.z_mem]
      refine ⟨n, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hdc, map_sum, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun q _ => ?_
      rw [← key, ← map_sub]
      exact spStab_valra X τ k _ _ hn
end

