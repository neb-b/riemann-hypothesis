module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AdFacts
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {k : Type} [CommRing k] {A B : M4 k} (hA : IsUp A) (hB : IsUp B) : IsUp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]

theorem UpperTheory.V.Ws.X1.adFacts :
    ∀ {k Γ : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), ((∀ i j, IsLocallyConstant fun g => r g i j) → IsOpen ((adSp r h).ker : Set Γ) ∧ ∀ X, IsLocallyConstant fun g => adSp r h g X) ∧ ∀ (n : M4 k) (s : Γ), IsGSp 1 n → IsUp (adj n * r s * n) → IsUp (adj n * r s⁻¹ * n) → ∀ X ∈ bor n, adSp r h s X ∈ bor n := by
  intro k Γ _ _ _ _ r h
  refine ⟨fun hloc => ?_, fun n s hn h1 h2 X hX => ?_⟩
  · have hr : IsLocallyConstant fun g => r g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro M
      have hset : (fun g => r g) ⁻¹' {M} = ⋂ i, ⋂ j, (fun g => r g i j) ⁻¹' {M i j} := by
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
        exact ⟨fun e i j => by rw [e], fun e => Matrix.ext e⟩
      rw [hset]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hloc i j).isOpen_fiber _
    refine ⟨?_, fun X => ?_⟩
    · have hker : IsOpen ((r.ker : Subgroup Γ) : Set Γ) := by
        have : ((r.ker : Subgroup Γ) : Set Γ) = (fun g => r g) ⁻¹' {1} := by
          ext g
          simp [MonoidHom.mem_ker]
        rw [this]
        exact hr.isOpen_fiber _
      refine Subgroup.isOpen_mono ?_ hker
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      apply LinearMap.ext
      intro Y
      apply Subtype.ext
      have hgi : r g⁻¹ = 1 := by
        have e := r.map_mul g⁻¹ g
        rw [inv_mul_cancel, r.map_one, hg, mul_one] at e
        exact e.symm
      rw [adSp_val, hg, hgi]
      simp
    · have hinv : IsLocallyConstant fun g => r g⁻¹ := hr.comp_continuous continuous_inv
      have hprod : IsLocallyConstant fun g => r g * (X : M4 k) * r g⁻¹ :=
        IsLocallyConstant.comp₂ (IsLocallyConstant.comp₂ hr (IsLocallyConstant.const (X : M4 k)) (· * ·)) hinv (· * ·)
      refine IsLocallyConstant.desc _ (fun Y : sp4 k => (Y : M4 k)) ?_ Subtype.val_injective
      convert hprod using 1
      funext g
      simp [adSp_val]
  · have hn' : n * adj n = 1 := by
      have e : adj n * n = 1 := by simpa [IsGSp] using hn
      exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.mp e
    show IsUp (adj n * ((adSp r h s X : sp4 k) : M4 k) * n)
    rw [adSp_val]
    have key : adj n * (r s * (X : M4 k) * r s⁻¹) * n
        = (adj n * r s * n) * (adj n * (X : M4 k) * n) * (adj n * r s⁻¹ * n) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul, ← Matrix.mul_assoc n (adj n), hn', Matrix.one_mul]
    rw [key]
    exact up_mul (up_mul h1 hX) h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ClosureComm
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem adj_up {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := fun i j h => by
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

private theorem adj_diag {R : Type} [CommRing R] (X : M4 R) (i : Fin 4) : adj X i i = X i.rev i.rev := by
  have h : sgn i * sgn i = 1 := by revert i; decide
  rw [adj_apply, h, one_smul]

private theorem gsp_diag {R : Type} [CommRing R] {ν : R} {n X : M4 R} (hn : IsGSp 1 n) (hX : IsGSp ν X)
    (hu : IsUp (adj n * X * n)) (i : Fin 4) : (adj n * X * n) i.rev i.rev * (adj n * X * n) i i = ν := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn
  have h2 : n * adj n = 1 := mul_eq_one_comm.1 h1
  have h3 : adj (adj n * X * n) * (adj n * X * n) = ν • (1 : M4 R) := by
    have hX' : adj X * X = ν • (1 : M4 R) := hX
    rw [hmul, hmul, hadj]
    calc adj n * (adj X * n) * (adj n * X * n) = adj n * (adj X * (n * adj n) * X) * n := by simp only [mul_assoc]
      _ = ν • (1 : M4 R) := by rw [h2, mul_one, hX', mul_smul_comm, mul_one, smul_mul_assoc, h1]
  have h4 := up_mul_diag (adj_up hu) hu i
  rw [adj_diag, h3] at h4
  simpa using h4.symm

private theorem closure_comm {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing R]
    (I : Ideal R) [IsHausdorff I R] (H : Subgroup Γ) (f : Γ → R) (h1 : f 1 = 1)
    (hm : ∀ s ∈ H, ∀ t ∈ H, f (s * t) = f s * f t) (hc : AdicCont I f) :
    ∀ c ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure, f c = 1 := by
  have hi : ∀ s ∈ H, f s * f s⁻¹ = 1 := fun s hs => by rw [← hm s hs _ (H.inv_mem hs), mul_inv_cancel, h1]
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ H ∧ f g = 1}
      one_mem' := ⟨H.one_mem, h1⟩
      mul_mem' := fun {s t} hs ht => ⟨H.mul_mem hs.1 ht.1, by rw [hm s hs.1 t ht.1, hs.2, ht.2, mul_one]⟩
      inv_mem' := fun {s} hs => ⟨H.inv_mem hs.1, by have := hi s hs.1; rwa [hs.2, one_mul] at this⟩ }
  have hK : ⁅H, H⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    have a1 := H.mul_mem hs ht
    have a2 := H.mul_mem a1 (H.inv_mem hs)
    rw [commutatorElement_def]
    refine ⟨H.mul_mem a2 (H.inv_mem ht), ?_⟩
    rw [hm _ a2 _ (H.inv_mem ht), hm _ a1 _ (H.inv_mem hs), hm _ hs _ ht]
    linear_combination (f t * f t⁻¹) * hi s hs + hi t ht
  intro c hcm
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun N => ?_
  have hcl := (hc N).isClosed_fiber (Ideal.Quotient.mk (I ^ N) 1)
  have : c ∈ {g | Ideal.Quotient.mk (I ^ N) (f g) = Ideal.Quotient.mk (I ^ N) 1} :=
    closure_minimal (fun g hg => by
      show Ideal.Quotient.mk (I ^ N) (f g) = _
      rw [(hK hg).2]) hcl hcm
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.1 this

private theorem conj_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (r : Γ → M4 R)
    (h : ∀ i j, AdicCont I fun g => r g i j) (A B : M4 R) (i j : Fin 4) : AdicCont I fun g => (A * r g * B) i j := by
  intro N
  have h0 : IsLocallyConstant fun g => (r g).map (Ideal.Quotient.mk (I ^ N)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun p : Fin 4 × Fin 4 => (h p.1 p.2 N).eventually_eq x
    filter_upwards [Filter.eventually_all.2 this] with y hy
    ext a b
    exact hy (a, b)
  have h2 := h0.comp fun X => (A.map (Ideal.Quotient.mk (I ^ N)) * X * B.map (Ideal.Quotient.mk (I ^ N))) i j
  convert h2 using 2 with g
  simp only [Function.comp_apply, ← Matrix.map_mul, Matrix.map_apply]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.muIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.noMu.Lifts a c P → (Φ.Lifts a c P ↔ ∀ v, P.ψ v 0 (ζ v) = 1 ∧ P.ψ v 1 (ζ v) = 1) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c _ ζ hζ hν R _ _ _ P hP
  refine ⟨fun h v => ⟨h.pair.mu v _ (hζ v).1 0, h.pair.mu v _ (hζ v).1 1⟩, fun h => ?_⟩
  obtain ⟨⟨hmult, hkill, hnrm, hlow, hflag, -⟩, hcont, hred⟩ := hP
  refine ⟨⟨hmult, hkill, hnrm, hlow, hflag, fun v s hs i => ?_⟩, hcont, hred⟩
  have hn : IsGSp 1 (P.n v) := (hlow v).1
  have n1 : adj (P.n v) * P.n v = 1 := by simpa [IsGSp] using hn
  have n2 : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.1 n1
  have hz : ζ v ∈ Φ.Gv v := (hS.mu v _ (hζ v).1).1
  have hsG : s ∈ Φ.Gv v := (hS.mu v _ hs).1
  have hrev : ∀ j : Fin 4, P.ψ v j.rev (ζ v) * P.ψ v j (ζ v) = 1 := fun j => by
    have := gsp_diag hn (hmult (ζ v)) (hflag v _ hz) j
    rw [RingHom.comp_apply] at this
    erw [hν v] at this
    rwa [map_one] at this
  have hzi : P.ψ v i (ζ v) = 1 := by
    have e0 := hrev 0
    have e1 := hrev 1
    rw [(h v).1, mul_one] at e0
    rw [(h v).2, mul_one] at e1
    fin_cases i
    exacts [(h v).1, (h v).2, e1, e0]
  have h1 : P.ψ v i 1 = 1 := by simp [PD.ψ, n1]
  have hm : ∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t := fun s hs t ht => by
    unfold PD.ψ
    rw [← up_mul_diag (hflag v s hs) (hflag v t ht), map_mul]
    refine congrFun (congrFun ?_ i) i
    calc adj (P.n v) * (P.r s * P.r t) * P.n v
        = adj (P.n v) * P.r s * (P.n v * adj (P.n v)) * P.r t * P.n v := by rw [n2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have hpow : ∀ n : ℕ, P.ψ v i (ζ v ^ n) = 1 := fun n => by
    induction n with
    | zero => rw [pow_zero, h1]
    | succ n ih => rw [pow_succ, hm _ (pow_mem hz n) _ hz, ih, hzi, mul_one]
  obtain ⟨n, hn'⟩ := (hζ v).2 s hs
  have hc := closure_comm (maximalIdeal R) (Φ.Gv v) (P.ψ v i) h1 hm
    (conj_cont _ (fun g => P.r g) hcont _ _ i i) _ hn'
  have := hm _ (mul_mem hsG (inv_mem (pow_mem hz n))) _ (pow_mem hz n)
  rwa [inv_mul_cancel_right, hc, hpow, mul_one] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.CoefEx
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.coefEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {A : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (κ : Type) [Fintype κ] (ε : κ → A), K = Ideal.span (Set.range ε) → (∀ c : κ → Λ, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal Λ) → ∃ co : κ → A → ResidueField Λ, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res Λ A a * co u x) ∧ ∀ x ∈ K, ∃ a : κ → Λ, (∀ u, residue Λ (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro Λ _ _ A _ _ _ K hK κ _ ε hspan hind
  classical
  have hkill : ∀ m ∈ maximalIdeal A, ∀ e ∈ K, m * e = 0 := by
    intro m hm e he
    have h := Ideal.mul_mem_mul hm he
    rw [hK] at h
    exact (Submodule.mem_bot A).mp h
  have hsc : ∀ b : A, ∃ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A := fun b => IsCO.res_surj (O := Λ) b
  have hact : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → ∀ e ∈ K, b * e = l • e := by
    intro b l hb e he
    have h := hkill _ hb e he
    rw [sub_mul] at h
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp h
  have hres : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → res Λ A b = residue Λ l := by
    intro b l hb
    have h := (res_eq_zero_iff Λ A _).mpr hb
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h
    rw [h]
    rfl
  have hex : ∀ x ∈ K, ∃ a : κ → Λ, x = ∑ u, a u • ε u := by
    intro x hx
    have hx' := hx
    rw [hspan] at hx'
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    choose l hl using fun u => hsc (b u)
    refine ⟨l, ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]
    refine hact _ _ (hl u) _ ?_
    rw [hspan]
    exact Ideal.subset_span ⟨u, rfl⟩
  have huniq : ∀ a a' : κ → Λ, ∑ u, a u • ε u = ∑ u, a' u • ε u →
      ∀ u, residue Λ (a u) = residue Λ (a' u) := by
    intro a a' h u
    have h0 := hind (a - a') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]) u
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h0
  let co : κ → A → ResidueField Λ := fun u x => if h : x ∈ K then residue Λ ((hex x h).choose u) else 0
  have hco : ∀ x (h : x ∈ K) (a : κ → Λ), x = ∑ u, a u • ε u → ∀ u, co u x = residue Λ (a u) := by
    intro x h a hx u
    simp only [co, dif_pos h]
    exact huniq _ _ ((hex x h).choose_spec.symm.trans hx) u
  refine ⟨co, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨b, hb⟩ := hex y hy
    rw [hco x hx a ha, hco y hy b hb, hco (x + y) (K.add_mem hx hy) (a + b)
      (by rw [ha, hb, ← Finset.sum_add_distrib]; simp [add_smul]), Pi.add_apply, map_add (f := _)]
  · intro u c x hx
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨l, hl⟩ := hsc c
    rw [hco x hx a ha, hco (c * x) (K.mul_mem_left c hx) (l • a) ?_, hres c l hl, Pi.smul_apply, smul_eq_mul,
      map_mul]
    rw [hact c l hl x hx, ha, Finset.smul_sum]
    simp [smul_smul]
  · intro x hx
    obtain ⟨a, ha⟩ := hex x hx
    exact ⟨a, fun u => (hco x hx a ha u).symm, ha⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ConeTan
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exProj {k W : Type} [Field k] [AddCommGroup W] [Module k W] (b n : Submodule k W)
    (h : IsCompl b n) : ∃ P : W →ₗ[k] W, (∀ x, P x ∈ n) ∧ ∀ x, P x - x ∈ b := by
  refine ⟨n.projection b h.symm, fun x => Submodule.projection_apply_mem _ x, fun x => ?_⟩
  have e := Submodule.projection_add_projection_eq_self h.symm x
  have hm : b.projection n h x ∈ b := Submodule.projection_apply_mem _ x
  have : n.projection b h.symm x - x = -(b.projection n h x) := by
    calc n.projection b h.symm x - x
        = n.projection b h.symm x - (n.projection b h.symm x + b.projection n h x) := by rw [e]
      _ = -(b.projection n h x) := by abel
  rw [this]
  exact b.neg_mem hm

private theorem dimLem {k W T H A : Type} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [AddCommGroup H] [Module k H] [AddCommGroup A] [Module k A] [Module.Finite k A]
    (t H0 : Submodule k W) (e : T →ₗ[k] W ⧸ t) (j : LinearMap.ker e →ₗ[k] A) (hj : Function.Injective j)
    (q : T →ₗ[k] H) (hq : Function.Surjective q) (f : W →ₗ[k] T) (hf : ∀ X, q (f X) = 0)
    (h0 : LinearMap.ker f ≤ H0) :
    Module.finrank k H + Module.finrank k t ≤ Module.finrank k A + Module.finrank k H0 := by
  haveI hK : Module.Finite k (LinearMap.ker e) := Module.Finite.of_injective j hj
  haveI hT : Module.Finite k T := by
    rw [← Module.rank_lt_aleph0_iff, ← LinearMap.rank_range_add_rank_ker e]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  have r1 := LinearMap.finrank_range_add_finrank_ker e
  have r2 := Submodule.finrank_le (LinearMap.range e)
  have r3 := Submodule.finrank_quotient_add_finrank t
  have r4 := LinearMap.finrank_le_finrank_of_injective hj
  have r5 := LinearMap.finrank_range_add_finrank_ker q
  have r6 : Module.finrank k (LinearMap.range q) = Module.finrank k H := by
    rw [LinearMap.range_eq_top.mpr hq, finrank_top]
  have hfq : LinearMap.range f ≤ LinearMap.ker q := by
    rintro _ ⟨X, rfl⟩
    exact hf X
  have r7 := Submodule.finrank_mono hfq
  have r8 := LinearMap.finrank_range_add_finrank_ker f
  have r9 := Submodule.finrank_mono h0
  omega

theorem UpperTheory.V.Ws.X1.coneTan :
    ∀ {k G W V : Type} [Field k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b n : V → Submodule k W) (g0 : G) (t : Submodule k W), (∀ X, IsLocallyConstant fun g => ρ g X) → (∀ v s, ∀ X ∈ b v, ρ (loc v s) X ∈ b v) → (∀ v, IsCompl (b v) (n v)) → Module.Finite k (TanC loc ρ b n g0 t) → Module.finrank k (Fr.H1C loc ρ b) + Module.finrank k t ≤ Module.finrank k (TanC loc ρ b n g0 t) + Module.finrank k (Fr.coneH0 ρ b) := by
  intro k G W V _ _ _ _ _ _ Gv _ loc ρ b n g0 t hlc hstab hcompl hfin
  choose P hPn hPb using fun v => exProj (b v) (n v) (hcompl v)
  have hPb' : ∀ v x, x - P v x ∈ b v := fun v x => by
    simpa using (b v).neg_mem (hPb v x)
  have hloc : ∀ v (s : Gv v) (y : W), y ∈ b v → ρ (loc v s) y - y ∈ b v := fun v s y hy =>
    (b v).sub_mem (hstab v s y hy) hy
  set S : Submodule k ((G → W) × (V → W)) :=
    Fr.Z1C loc ρ b ⊓ Submodule.comap (LinearMap.snd k (G → W) (V → W)) (Submodule.pi Set.univ n) with hSd
  let q : S →ₗ[k] Fr.H1C loc ρ b :=
    (Submodule.mkQ _) ∘ₗ Submodule.inclusion (inf_le_left : S ≤ Fr.Z1C loc ρ b)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨⟨c, x⟩, hz⟩ := z
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hmem : ((c, fun v => P v (x v)) : (G → W) × (V → W)) ∈ S := by
      refine ⟨⟨hz1, hz2, fun v s => ?_⟩, ?_⟩
      · have h1 := hz3 v s
        have h2 := hloc v s _ (hPb v (x v))
        have e : c (loc v s) - (ρ (loc v s) (P v (x v)) - P v (x v)) =
            (c (loc v s) - (ρ (loc v s) (x v) - x v)) -
              (ρ (loc v s) (P v (x v) - x v) - (P v (x v) - x v)) := by
          rw [map_sub]; abel
        simp only at h1 ⊢
        rw [e]
        exact (b v).sub_mem h1 h2
      · simp [Submodule.mem_pi, hPn]
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨0, fun s => ?_, fun v => ?_⟩
    · simp
    · simpa using hPb v (x v)
  have fmem : ∀ X : W, ((fun s => ρ s X - X, fun v => P v X) : (G → W) × (V → W)) ∈ S := by
    intro X
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hlc X).sub (IsLocallyConstant.const X)
    · intro s u
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro v s
      have h2 := hloc v s _ (hPb' v X)
      have e : (ρ (loc v s) X - X) - (ρ (loc v s) (P v X) - P v X) =
          ρ (loc v s) (X - P v X) - (X - P v X) := by
        rw [map_sub]; abel
      simp only
      rw [e]
      exact h2
    · simp [Submodule.mem_pi, hPn]
  let f : W →ₗ[k] S :=
    { toFun := fun X => ⟨_, fmem X⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        ext s <;> simp <;> abel
      map_smul' := fun a X => by
        apply Subtype.ext
        ext s <;> simp [smul_sub] }
  have hf : ∀ X, q (f X) = 0 := by
    intro X
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨X, fun s => rfl, fun v => hPb v X⟩
  have h0 : LinearMap.ker f ≤ Fr.coneH0 ρ b := by
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have h1 := congrArg (fun z : S => z.1.1) hX
    have h2 := congrArg (fun z : S => z.1.2) hX
    refine ⟨fun g => ?_, fun v => ?_⟩
    · have := congrFun h1 g
      simp [f] at this
      exact sub_eq_zero.mp this
    · have := congrFun h2 v
      have hb := hPb v X
      simp [f] at this
      rw [this, zero_sub] at hb
      simpa using (b v).neg_mem hb
  let e : S →ₗ[k] W ⧸ t :=
    t.mkQ ∘ₗ (LinearMap.proj g0 ∘ₗ LinearMap.fst k (G → W) (V → W)) ∘ₗ S.subtype
  have jmem : ∀ z : LinearMap.ker e, (z.1.1 : (G → W) × (V → W)) ∈ TanC loc ρ b n g0 t := by
    rintro ⟨⟨z, hz1, hz2⟩, hze⟩
    rw [LinearMap.mem_ker] at hze
    refine ⟨hz1, ?_, ?_⟩
    · simpa [e, Submodule.Quotient.mk_eq_zero] using hze
    · exact hz2
  let j : LinearMap.ker e →ₗ[k] TanC loc ρ b n g0 t :=
    LinearMap.codRestrict _ (S.subtype ∘ₗ (LinearMap.ker e).subtype) jmem
  have hj : Function.Injective j := by
    intro z z' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite k (TanC loc ρ b n g0 t) := hfin
  exact dimLem t (Fr.coneH0 ρ b) e j hj q hq f hf h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ (I : Submodule R R)) :=
    ⟨by simpa [smul_eq_mul] using hxm, hxI⟩
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hmem : x ∈ maximalIdeal R • (I : Submodule R R) := Submodule.smul_mono le_rfl inf_le_right hx
  rw [smul_eq_mul, h] at hmem
  simpa using hmem

theorem UpperTheory.V.Ws.X1.contLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → (∀ (S : Type) [TopologicalSpace S] (x : S → R), AdicCont (maximalIdeal R) x → ∃ y : S → A, AdicCont (maximalIdeal A) y ∧ ∀ s, p (y s) = x s) ∧ ∀ (S : Type) [TopologicalSpace S] (y : S → A), AdicCont (maximalIdeal A) y → (∀ s, p (y s) = 0) → IsLocallyConstant y := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p hp hK
  haveI : IsNoetherianRing A := IsCO.toIsNoetherian Λ
  obtain ⟨N0, hN0⟩ := inf_pow_bot A (RingHom.ker p) hK
  have hm : ∀ a : A, a ∈ maximalIdeal A ↔ p a ∈ maximalIdeal R := by
    intro a
    rw [← res_eq_zero_iff Λ A, ← res_eq_zero_iff Λ R, res_map]
  have hmap1 : Ideal.map p (maximalIdeal A) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hm a).mp ha
    · intro hr
      obtain ⟨a, rfl⟩ := hp r
      exact ⟨a, (hm a).mpr hr, rfl⟩
  have hmap : ∀ n, ∀ r ∈ maximalIdeal R ^ n, ∃ z ∈ maximalIdeal A ^ n, p z = r := by
    intro n r hr
    rw [← hmap1, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective p hp] at hr
    exact hr
  choose ρ hρ using fun c : R ⧸ maximalIdeal R ^ N0 => Ideal.Quotient.mk_surjective c
  choose l hl using fun c : R ⧸ maximalIdeal R ^ N0 => hp (ρ c)
  have hu : ∀ r : R, ∃ z ∈ maximalIdeal A ^ N0, p z = r - ρ (Ideal.Quotient.mk _ r) := by
    intro r
    apply hmap
    rw [← Ideal.Quotient.eq, hρ]
  choose u hu1 hu2 using hu
  let σ : R → A := fun r => l (Ideal.Quotient.mk _ r) + u r
  have hpσ : ∀ r, p (σ r) = r := by
    intro r
    simp only [σ, map_add (f := _), hl, hu2]
    ring
  have hL : ∀ M, N0 ≤ M → ∀ r r' : R, r - r' ∈ maximalIdeal R ^ M → σ r - σ r' ∈ maximalIdeal A ^ M := by
    intro M hM r r' h
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N0) r) = Ideal.Quotient.mk _ r' :=
      Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hM h)
    obtain ⟨z, hz, hpz⟩ := hmap M _ h
    have hzero : z - (u r - u r') = 0 := by
      apply hN0
      · rw [RingHom.mem_ker]
        simp only [map_sub]
        rw [hpz, hu2, hu2, hq]
        ring
      · exact sub_mem (Ideal.pow_le_pow_right hM hz) (sub_mem (hu1 r) (hu1 r'))
    have hz' : u r - u r' = z := (sub_eq_zero.mp hzero).symm
    simp only [σ]
    rw [hq, add_sub_add_left_eq_sub, hz']
    exact hz
  refine ⟨?_, ?_⟩
  · intro S _ x hx
    refine ⟨fun s => σ (x s), ?_, fun s => hpσ _⟩
    intro n
    have hc := hx (max n N0)
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 := hL (max n N0) (le_max_right _ _) _ _ h1
    exact Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right (le_max_left _ _) h2)
  · intro S _ y hy h0
    have hc := hy N0
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 : y s' - y s = 0 := by
      apply hN0 _ _ h1
      rw [RingHom.mem_ker, map_sub, h0, h0, sub_zero]
    exact sub_eq_zero.mp h2
end

