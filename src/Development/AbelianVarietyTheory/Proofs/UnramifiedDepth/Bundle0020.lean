module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0029
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.DualLattices.IsFibreSq
public import ReciprocityTheory.DualLattices.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartPSmulLiftEqBt
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {g : ℕ} {V : Type} [AddCommGroup V] [Module R₀ V]

private def btTanCrd (gb : Module.Basis (Fin g) R₀ V) (M : Type) [AddCommGroup M] [Module R₀ M]
    (k : Fin g) : V ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M (gb.coord k)

private lemma btTanCrd_tmul (gb : Module.Basis (Fin g) R₀ V) {M : Type} [AddCommGroup M]
    [Module R₀ M] (k : Fin g) (w : V) (m : M) :
    btTanCrd gb M k (w ⊗ₜ m) = gb.repr w k • m := by
  simp [btTanCrd]

private lemma btTanCrd_nat (gb : Module.Basis (Fin g) R₀ V) {M N : Type} [AddCommGroup M]
    [Module R₀ M] [AddCommGroup N] [Module R₀ N] (f : M →ₗ[R₀] N) (k : Fin g) (v : V ⊗[R₀] M) :
    btTanCrd gb N k (LinearMap.lTensor V f v) = f (btTanCrd gb M k v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]

private lemma btTanCrd_base (gb : Module.Basis (Fin g) R₀ V) {S : Type} [CommRing S]
    [Algebra R₀ S] (k : Fin g) (v : V ⊗[R₀] S) :
    (Module.Basis.baseChange S gb).repr (TensorProduct.comm R₀ V S v) k = btTanCrd gb S k v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul w m => simp [btTanCrd_tmul]
  | add x y hx hy => simp [hx, hy]

end

private lemma btTan_chi_tg {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀}
    (ch : FormalChartAtZero B K g) {R S : LAlg R₀}
    (hF : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) →
      ∃ M : Matrix (Fin g) (Fin g) (R : Type),
        (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) (R : Type)) k j ∈ Ideal.span (Set.range a)) ∧
        ∀ e : Fin g → (R : Type), (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e)
    (ρ : LHom R K) (hρ : IsNilOver ρ) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (v : B.gg ⊗[R₀] π.ker) (k : Fin g) :
    ((ch.χ ρ hρ ⟨B.tg π hπ v, map_tg_ker B ρ π hπ ρS hfac _⟩ k : maximalIdeal (R : Type)) :
      (R : Type)) = (btTanCrd ch.gb π.ker k v : (R : Type)) := by
  have hmul : ∀ x ∈ RingHom.ker π.1, ∀ y ∈ RingHom.ker π.1, x * y = 0 := by
    intro x hx y hy
    have := Ideal.mul_mem_mul hx hy
    rw [← pow_two, hπ.2] at this
    exact this
  induction v using TensorProduct.induction_on generalizing k with
  | zero =>
    have := ch.χ_tg ρ hρ π hπ ρS hfac 0 0 k
    simpa using this
  | tmul w m =>
    rw [ch.χ_tg ρ hρ π hπ ρS hfac w m k, btTanCrd_tmul]; rfl
  | add x y hx hy =>
    have h := congrFun (ch.χ_add ρ hρ ⟨B.tg π hπ x, map_tg_ker B ρ π hπ ρS hfac _⟩
      ⟨B.tg π hπ y, map_tg_ker B ρ π hπ ρS hfac _⟩) k
    simp only [hx, hy] at h
    obtain ⟨M, hM, hMe⟩ := hF (fun k => (btTanCrd ch.gb π.ker k x : (R : Type)))
      (fun i => ⟨2, by rw [pow_two]; exact hmul _ (btTanCrd ch.gb π.ker i x).2 _ (btTanCrd ch.gb π.ker i x).2⟩)
    rw [hMe _ (fun i j => hmul _ (btTanCrd ch.gb π.ker i y).2 _ (btTanCrd ch.gb π.ker j y).2)] at h
    have hle : Ideal.span (Set.range fun k => (btTanCrd ch.gb π.ker k x : (R : Type))) ≤
        RingHom.ker π.1 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (btTanCrd ch.gb π.ker i x).2
    have h0 : ((M - 1) *ᵥ fun k => (btTanCrd ch.gb π.ker k y : (R : Type))) k = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      exact hmul _ (hle (hM k j)) _ (btTanCrd ch.gb π.ker j y).2
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at h0
    rw [Pi.add_apply, h0] at h
    simp only [map_add (f := _), Submodule.coe_add]
    exact h

theorem chart_p_smul_lift_eq_bt :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) := by
  intro hF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D t
  choose th w hth hpth hw using fun i => D.L.bt_spec i 1
  have hsq : D.wd.πW.SqZero := D.wd.πW.sqZero_of_span (p : (D.wd.W : Type)) D.wd.πW_surj
    D.wd.ker_πW (by rw [← pow_two]; exact D.wd.p_sq)
  have hc1 : D.wd.πW.comp D.wd.ψ = (Tw.r 0).comp (Tw.π 1) :=
    Subtype.ext (AlgHom.ext fun a => D.wd.compat a)
  have hc2 : (Tw.r 0).comp (Tw.q 1) = Tw.q 0 :=
    Subtype.ext (AlgHom.ext fun a => Tw.r_q 0 a)
  have hf : ∀ a ∈ (Tw.π 1).ker, D.wd.ψ.1.toLinearMap a ∈ D.wd.πW.ker := by
    intro a ha
    change D.wd.πW.1 (D.wd.ψ.1 a) = 0
    change (Tw.π 1).1 a = 0 at ha
    rw [D.wd.compat, ha, map_zero]
  let n : Ix g → ℕ := fun i => (red p g t i).val
  let v : B.gg ⊗[R₀] D.wd.πW.ker := ∑ i, n i • LinearMap.lTensor B.gg
    (D.wd.ψ.1.toLinearMap.restrict hf)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π 1) (Tw.ξ 1) (Tw.ξ_mem 1)) (w i))
  have hpt : p • ∑ i, n i • B.map D.wd.ψ (p • th i) = B.tg D.wd.πW hsq v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_sum, map_nsmul (B.tg D.wd.πW hsq), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [B.tg_nat (Tw.π 1) D.wd.πW (Tw.sqZero 1) hsq, ← hpth, smul_comm p, ← map_nsmul,
      smul_smul, pow_two]
  refine ⟨∑ i, n i • B.map D.wd.ψ (p • th i), ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [ptOf, map_sum, map_nsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← B.map_comp, hc1, B.map_comp, hth, ← B.map_comp, hc2, D.L.τ_compat i 0, map_nsmul]
  · refine ⟨hpt ▸ map_tg_ker B _ _ hsq _ D.wd.ρW_eq v, fun k => ?_⟩
    refine ⟨∑ i, n i • D.wd.ψ.1 (btTanCrd D.ch.gb _ k (w i)), ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_nsmul, Matrix.mulVec, dotProduct, map_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := congrArg (btTanCrd D.ch.gb _ k) (hw i)
      rw [btTanCrd_nat, btTanCrd_nat] at h1
      simp only [AlgHom.toLinearMap_apply] at h1
      rw [D.wd.compat, h1, Tw.r_q, D.L.Bt_eq, btTanCrd_base]
      have h2 : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) (t i)) = (n i : (Tw.R 0 : Type)) := by
        have h3 : t i - (n i : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
          rw [RingHom.mem_ker, map_sub, map_natCast]
          simp only [n, red]
          rw [ZMod.natCast_zmod_val, sub_self]
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
        obtain ⟨c, hc⟩ := h3
        have hp0 : (Tw.q 0).1 (p : (Tw.O : Type)) = 0 := by
          rw [← RingHom.mem_ker, D.tower_zero_ker]; exact Ideal.subset_span rfl
        rw [eq_add_of_sub_eq hc.symm]
        simp only [map_add (f := _), map_mul, map_natCast (algebraMap ℤ_[p] (Tw.O : Type)), hp0]
        simp
      rw [h2, nsmul_eq_mul, mul_comm]
    · have h := btTan_chi_tg D.ch (hF D.ch _) D.wd.ρW D.sm.nil D.wd.πW hsq D.wd.ρ1 D.wd.ρW_eq v k
      simp only [hpt]
      rw [h]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum, map_nsmul, AddSubmonoidClass.coe_finsetSum,
        AddSubmonoidClass.coe_nsmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [btTanCrd_nat, ← LinearMap.lTensor_def, btTanCrd_nat, ← D.wd.ξ_img, mul_smul_comm,
        ← map_mul]
      congr 1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffCoordinatesGoodTangentsLtSq
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)

noncomputable section

namespace GlobalTheory.MainTerm

theorem sum_pow_trunc_lt_sq {C : Type} [Field C] {I ι : Type} [Fintype I] {l : ℕ} (hl : 2 ≤ l)
    (T : I → MvPowerSeries ι C) (hT : ∀ c, OrdGE 1 (T c)) (f : I → ℕ → C) (μ : ι →₀ ℕ)
    (hμ : μ.degree < l ^ 2) :
    ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ c, f c 0 * MvPowerSeries.coeff μ (T c) + ∑ c, f c 1 * MvPowerSeries.coeff μ (T c ^ l) := by
  have h1 : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ s ∈ Finset.range (μ.degree + 1 + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) := by
    rw [Finset.sum_range_succ _ (μ.degree + 1), Finset.sum_eq_zero (s := Finset.univ), add_zero]
    intro c _
    rw [(hT c).pow _ μ ((Nat.lt_succ_self _).trans (Nat.lt_pow_self (by omega))), mul_zero]
  rw [h1, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, add_comm]
  · simp
  · intro s _
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [(hT c).pow _ μ (hμ.trans_le (Nat.pow_le_pow_right (by omega) (by omega))), mul_zero]

theorem ordGE_one_of_constantCoeff {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by
  intro A hA
  have : A = 0 := (Finsupp.degree_eq_zero_iff A).1 (by omega)
  subst this
  simpa using h

theorem sum_coeff_pow_ite {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map em)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    simp
  · intro c _ hc
    have h : ∀ δ, em δ ≠ c := fun δ h => hc (Finset.mem_map.2 ⟨δ, Finset.mem_univ _, h⟩)
    simp [h, hn]

theorem coeff_low_good : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  intro C _ V d I J _ _ G S t ht N em hem
  have hl : 2 ≤ V.l := V.l_prime.two_le
  let al : I → ℕ → I → C := fun c k b =>
    if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if em j = b then 1 else 0) al
    (by intro j x; simp)
    (by intro c b; simp [al])
    (by
      intro c k x hk
      have hk' : k ≠ 0 := by omega
      simp only [al, hk', if_false, Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  set T : I → MvPowerSeries (Fin N) C := fun c => linPull (fun δ => S.tan (em δ)) (t c) with hTdef
  set z : I → MvPowerSeries (Fin N) C := fun c =>
    ∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0 with hz
  have hT : ∀ c, OrdGE 1 (T c) := fun c => ordGE_one_of_constantCoeff (h0 c)
  have hz1 : ∀ c, OrdGE 1 (z c) := fun c => by
    refine OrdGE.sum _ fun δ _ => ?_
    split_ifs
    · exact OrdGE.X δ
    · exact OrdGE.zero
  have hal1 : ∀ δ b, al (em δ) 1 b = 0 := fun δ b => by
    have : ∀ x, S.cur (em δ) 1 (Sum.inl x) = 0 := hem δ
    simp [al, Sys.co, this]
  have key : ∀ D, D + 1 ≤ V.l ^ 2 → ∀ c, OrdGE (D + 1) (T c - z c) := by
    intro D
    induction D with
    | zero => exact fun _ c => (hT c).sub (hz1 c)
    | succ D ih =>
      intro hD b A hA
      have e := h1 b A
      have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => al c s b) A (by omega)
      rw [e2] at e
      have e3 : ∀ c, MvPowerSeries.coeff A (T c ^ V.l) = MvPowerSeries.coeff A (z c ^ V.l) := fun c => by
        have := OrdGE.pow_sub_pow (hT c) (hz1 c) (ih (by omega) c) (N := V.l) (by omega) A (by omega)
        rwa [map_sub, sub_eq_zero] at this
      have e4 : ∑ c, al c 1 b * MvPowerSeries.coeff A (T c ^ V.l) = 0 := by
        simp only [e3, hz]
        rw [sum_coeff_pow_ite em (fun c => al c 1 b) (by omega)]
        simp [hal1]
      rw [e4, add_zero] at e
      rw [map_sub, sub_eq_zero]
      have e5 : ∑ c, al c 0 b * MvPowerSeries.coeff A (T c) = MvPowerSeries.coeff A (T b) := by
        simp [al]
      rw [← e5, e]
      congr 1
      refine Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp
  intro μ hμ
  refine ⟨fun c => ?_, fun κ => ?_⟩
  · have := key μ.degree hμ c μ (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  · have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => S.be c s κ) μ hμ
    have e3 : ∀ c, MvPowerSeries.coeff μ (T c ^ V.l) = MvPowerSeries.coeff μ (z c ^ V.l) := fun c => by
      have := OrdGE.pow_sub_pow (hT c) (hz1 c) (key μ.degree hμ c) (N := V.l) (by omega) μ (by omega)
      rwa [map_sub, sub_eq_zero] at this
    rw [h2 κ μ, e2]
    simp only [e3, hz]
    rw [sum_coeff_pow_ite em (fun c => S.be c 1 κ) (by omega)]
    simp [Sys.be, S.be_zero]

end GlobalTheory.MainTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualTowerMapExists
section
noncomputable section

namespace GlobalTheory

section Helpers

open ReciprocityTheory.PGsh

private def dualTowerRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma dualTowerRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    dualTowerRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [dualTowerRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma dualTowerRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : dualTowerRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [dualTowerRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma dualTowerRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (dualTowerRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [dualTowerRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | monomial n a _ =>
    have h := dualTowerRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma dualTower_map_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { dualTowerRing Dq ψ with
      commutes' := fun r => by
        show dualTowerRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => dualTowerRing_π Dq ψ x,
    fun x => ?_, dualTowerRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (dualTowerRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((dualTowerRing_π Dq ψ a) ▸ h1)
  · show dualTowerRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C]
    rfl

private lemma dualTower_nonempty {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p) :
    Nonempty (DualTower Tw) := by
  choose d h₁ h₂ h₃ using fun n => dualTower_map_exists (DualNum.dualPair (Tw.R n)) (Tw.r n)
  exact ⟨⟨fun n => DualNum.dualPair (Tw.R n), d, h₁, h₂, h₃⟩⟩

end Helpers

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_dualTower :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p), Nonempty (DualTower Tw)) :=
  fun Tw => dualTower_nonempty Tw

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvImgIsLatSubring
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

end


open TensorProduct IsLocalRing Matrix in
theorem _root_.GlobalTheory.evImg_isLat_subring :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement
  intro C _ _ hdom hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => by
        have h := congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 o) (hspec t).1
        exact h }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  haveI : ∀ i, Module.Free Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).1
  haveI : ∀ i, Module.Finite Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).2
  haveI := hdom
  have hrank : Module.finrank Tw.O.carrier (∀ i, (D.fin.AAx i).carrier) = Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [Module.finrank_pi_fintype, ← Nat.card_eq_fintype_card]
    refine Eq.trans ?_ (D.fin.rank.trans (Nat.card_congr (Equiv.ofBijective _ D.L.τ_basis)).symm)
    rfl
  let b0 := Module.Free.chooseBasis Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)) =
      Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  let b := b0.reindex (Fintype.equivOfCardEq hcard)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.PGsh.L2.IsLat
    refine ⟨Matrix.of fun x j => f (b j) x, ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      have hdet : (Matrix.of fun x j => f (b j) x).det =
          algebraMap Tw.O.carrier C (Matrix.of fun x j => Ψ (b j) x).det := by
        rw [RingHom.map_det]; rfl
      rw [hdet]
      intro h0
      rw [← map_zero (algebraMap Tw.O.carrier C)] at h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hinj h0)
      apply hv0
      have hsum : Ψ (∑ j, v j • b j) = 0 := by
        rw [← hv]
        funext x
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]
      have h1 : ∑ j, v j • b j = 0 := hinjΨ (by rw [hsum, map_zero])
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent v h1 j
    · rw [himg]
      change _ = Submodule.span _ (Set.range (f ∘ b))
      rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rw [himg]
    rintro _ ⟨F, rfl⟩
    exact fun x => ⟨_, (hf F x).symm⟩
  · rw [himg]
    exact ⟨1, by funext x; simp only [hf, Pi.one_apply, map_one]⟩
  · rw [himg]
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨F * G, by funext x; simp only [hf, Pi.mul_apply, map_mul]⟩

end GlobalTheory
end
end

