module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0001
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0004
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.LocLanglands
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem twKer_twoBlocks_eq_top (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n a : ℕ} (h0 : 0 < a) (ha : a < n)
    (τ : FDRep ℂ (Gn g n)) (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 = ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hs
  have hgen : ∀ x : GL (Fin n) k, x ∈ GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) → ∀ v,
      σ.ρ x v - v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro x hx v
    refine Submodule.subset_span ⟨⟨x, hx⟩, v, ?_⟩
    simp
  have hφT : ∀ w, φ w ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro w
    have hfin := sum_unip_eq_zero τ hτ h0 ha
    have key : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        φ w - φ (τ.ρ (u : Gn g n) w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
      intro u
      obtain ⟨κ, hred, hmem⟩ := exists_lift i (u : Gn g n) u.2
      have h1 := hφ κ w
      rw [hred] at h1
      rw [h1, ← neg_sub]
      exact Submodule.neg_mem _ (hgen _ hmem (φ w))
    have hsum : ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        (φ w - φ (τ.ρ (u : Gn g n) w)) =
          (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) • φ w := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, ← map_sum φ (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n) w),
        ← LinearMap.sum_apply Finset.univ
          (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n)) w, hfin, LinearMap.zero_apply, map_zero,
        sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hc : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hmem := Submodule.sum_mem _ fun u (_ : u ∈ Finset.univ) => key u
    rw [hsum] at hmem
    have := Submodule.smul_mem _
      (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ (h : GL (Fin n) k) (w : τ),
      σ.ρ h (φ w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro h w
    obtain ⟨p, hp, k0, hk0, rfl⟩ :=
      GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL k n (monotone_twoBlocks (N := n) a) h
    obtain ⟨κ, rfl⟩ := exists_inc_eq i hi k0 hk0
    rw [map_mul, Module.End.mul_apply]
    refine twKer_le_comap σ.ρ _ p (blockUpper_le_normalizer (GlobalTheory.FiniteGL.twoBlocks n a) hp) ?_
    have h1 := hφ κ w
    rw [show (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ w) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) (φ w) from rfl] at h1
    rw [← h1]
    exact hφT _
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  let S : Subrepresentation σ.ρ :=
    ⟨Submodule.span ℂ {v | ∃ (h : GL (Fin n) k) (w : τ), v = σ.ρ h (φ w)}, fun x v hv => by
      refine (Submodule.span_le.2 ?_ : _ ≤ (Submodule.span ℂ _).comap (σ.ρ x)) hv
      rintro _ ⟨h, w, rfl⟩
      exact Submodule.subset_span ⟨x * h, w, by rw [map_mul, Module.End.mul_apply]⟩⟩
  have hST : S.toSubmodule ≤ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨h, w, rfl⟩; exact hall h w)
  have hirr := σ.irr
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hm : φ w0 ∈ S.toSubmodule := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
    rw [hS] at hm
    exact hw0 ((Submodule.mem_bot ℂ).1 hm)
  · refine eq_top_iff.2 fun v _ => hST ?_
    rw [hS]
    trivial

theorem isCuspidal_of_inflates (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (τ : FDRep ℂ (Gn g n))
    (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    IsCuspidal σ.ρ := by
  refine ⟨σ.smooth, fun s d e he => ?_⟩
  obtain ⟨Q, a, h0, ha, hQ⟩ := exists_perm_conj e he
  have htop := twKer_twoBlocks_eq_top i hi h0 ha τ hτ σ hs
  have hinvQ : ∀ z, σ.ρ Q⁻¹ (σ.ρ Q z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 ≤
      (twKer σ.ρ (unipRad k e) 1).comap (σ.ρ Q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, y, rfl⟩
    refine Submodule.subset_span ⟨⟨Q * x * Q⁻¹, hQ x hx⟩, σ.ρ Q y, ?_⟩
    simp [map_mul, Module.End.mul_apply, hinvQ]
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have hv : σ.ρ Q⁻¹ v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    rw [htop]
    exact Submodule.mem_top
  have := hmap hv
  rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at this

end DiscreteGroups.sglob.DzLc

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def nmChar {g : ℕ} (K : Type) [Field K] [Algebra (ZMod g) K] (χ : (ZMod g)ˣ →* ℂˣ) : Kˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm (ZMod g) : K →* ZMod g))

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConv
section
noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem altIdentity : AltIdentity := by
  intro G _ _ _ K hKo hKc _ N hN H _ _ _ π hπ e he hKe hfix d hd g
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hd
    exact Nat.not_lt_zero _ hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd0
  have hstar : ∀ a, star (π a) = π a⁻¹ := alt_star_eq π hπ
  have hes : star e = e := he.star_eq
  have hKe' : ∀ κ ∈ K, π κ * e = e := fun κ hκ => ContinuousLinearMap.ext fun x => hKe x κ hκ
  have hee : e * e = e := ContinuousLinearMap.ext fun x => hfix (e x) fun κ hκ => hKe x κ hκ
  have heK : ∀ κ ∈ K, e * π κ = e := by
    intro κ hκ
    have h1 := hKe' κ⁻¹ (K.inv_mem hκ)
    calc e * π κ = star (π κ⁻¹ * e) := by rw [star_mul, hes, hstar, inv_inv]
      _ = e := by rw [h1, hes]
  let f : G → (H →L[ℂ] H) := fun a => e * π a * e
  let Y : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ (Set.range fun a => π a * e)
  have hY1 : ∀ a, ∀ y ∈ Y, π a * y ∈ Y := by
    intro a y hy
    have : Y ≤ Y.comap (LinearMap.mulLeft ℂ (π a)) := Submodule.span_le.mpr (by
      rintro _ ⟨b, rfl⟩
      show π a * (π b * e) ∈ Y
      exact Submodule.subset_span ⟨a * b, by simp only [map_mul, mul_assoc]⟩)
    exact this hy
  have hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨K.comap (MulAut.conj a⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
      · have : ((K.comap (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun h => a⁻¹ * h * a) ⁻¹' (K : Set G) := by
          ext h; simp
        rw [this]
        exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · have hu' : a⁻¹ * u * a ∈ K := by simpa [MulAut.conj_apply] using hu
        calc π u * (π a * e) = π (u * a) * e := by rw [map_mul, mul_assoc]
          _ = π (a * (a⁻¹ * u * a)) * e := by rw [show a * (a⁻¹ * u * a) = u * a by group]
          _ = π a * (π (a⁻¹ * u * a) * e) := by rw [map_mul, mul_assoc]
          _ = π a * e := by rw [hKe' _ hu']
    | zero => exact ⟨⊤, by simp, fun u _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨U₁, h1o, h1⟩ := hx
      obtain ⟨U₂, h2o, h2⟩ := hz
      refine ⟨U₁ ⊓ U₂, by rw [Subgroup.coe_inf]; exact h1o.inter h2o, fun u hu => ?_⟩
      rw [mul_add, h1 u hu.1, h2 u hu.2]
    | smul c x _ hx =>
      obtain ⟨U, ho, h⟩ := hx
      exact ⟨U, ho, fun u hu => by rw [mul_smul_comm, h u hu]⟩
  have hYe : ∀ y ∈ Y, y * e = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; simp only [mul_assoc, hee]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul, hx, hz]
    | smul c x _ hx => rw [smul_mul_assoc, hx]
  have heY : e ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hE : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) → ∀ z ∈ Z, e * z ∈ Z := by
    intro Z hZY hZ z hz
    obtain ⟨U, hUo, hU⟩ := hSm z (hZY hz)
    exact alt_avg K hKc π e heK hfix Z (fun κ _ => hZ κ) z hz U hUo hU
  have hYE : ∀ y ∈ Y, e * y ∈ Y := hE Y le_rfl hY1
  have hYmul : ∀ x ∈ Y, ∀ y ∈ Y, x * y ∈ Y := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      show π a * e * y ∈ Y
      rw [mul_assoc]; exact hY1 a _ (hYE y hy)
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact Y.add_mem hx hz
    | smul c x _ hx => rw [smul_mul_assoc]; exact Y.smul_mem c hx
  have hword : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ l : List G, ∀ z ∈ Z, (l.map f).prod * z ∈ Z := by
    intro Z hZY hZ l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons a l ih =>
      intro z hz
      rw [List.map_cons, List.prod_cons, mul_assoc]
      show e * π a * e * ((l.map f).prod * z) ∈ Z
      rw [mul_assoc, mul_assoc]
      exact hE Z hZY hZ _ (hZ a _ (hE Z hZY hZ _ (ih z hz)))
  have hfstar : ∀ a, star (f a) = f a⁻¹ := by
    intro a
    show star (e * π a * e) = e * π a⁻¹ * e
    simp only [star_mul, hes, hstar, mul_assoc]
  have hwstar : ∀ l : List G, star ((l.map f).prod) = ((l.reverse.map (·⁻¹)).map f).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, ih, hfstar]
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f := by
    intro σ; rw [List.map_ofFn]; rfl
  set S := ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun i => e * π (g (σ i)) * e).prod with hSdef
  have hSZ : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ z ∈ Z, S * z ∈ Z ∧ star S * z ∈ Z := by
    intro Z hZY hZ z hz
    constructor
    · rw [hSdef, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [smul_mul_assoc, hterm]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
    · rw [hSdef, star_sum, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [star_smul, star_intCast, hterm, hwstar, smul_mul_assoc]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
  have hQ : ∀ (l : List G) a, f a * (l.map f).prod * e = f a * (l.map f).prod := by
    intro l
    induction l with
    | nil =>
      intro a
      simp only [List.map_nil, List.prod_nil, mul_one]
      show e * π a * e * e = e * π a * e
      rw [mul_assoc, hee]
    | cons b l ih => intro a; rw [List.map_cons, List.prod_cons, mul_assoc (f a), ih b]
  have hSe : S * e = S := by
    rw [hSdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, hterm, List.ofFn_succ, List.map_cons, List.prod_cons, hQ]
  have heSs : e * star S = star S := by
    have := congrArg star hSe
    rwa [star_mul, hes] at this
  have hSY : S ∈ Y := by rw [← hSe]; exact (hSZ Y le_rfl hY1 e heY).1
  by_contra hS
  have : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne S 0 hS
  set c := star S * S with hc
  have hcsa : IsSelfAdjoint c := IsSelfAdjoint.star_mul_self S
  have hc0 : c ≠ 0 := by
    intro h0
    have : ‖S‖ * ‖S‖ = 0 := by rw [← CStarRing.norm_star_mul_self, ← hc, h0, norm_zero]
    exact hS (norm_eq_zero.mp (mul_self_eq_zero.mp this))
  have hec : e * c = c := by rw [hc, ← mul_assoc, heSs]
  have hcY : c ∈ Y := (hSZ Y le_rfl hY1 S hSY).2
  obtain ⟨z, hz, hzn⟩ := spectrum.exists_nnnorm_eq_spectralRadius c
  rw [hcsa.spectralRadius_eq_nnnorm] at hzn
  have hz0 : z ≠ 0 := by
    intro h0
    apply hc0
    rw [h0, nnnorm_zero, ENNReal.coe_zero, eq_comm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hzn
    exact hzn
  have hzr : star z = z := by
    rw [hcsa.mem_spectrum_eq_re hz]
    exact Complex.conj_ofReal _
  have hnotl : ∀ y ∈ Y, y * (c - z • e) ≠ e := by
    intro y hy hyu
    set b := e * y with hb
    have hbe : b * e = b := by rw [hb, mul_assoc, hYe y hy]
    have hbu : b * (c - z • e) = e := by rw [hb, mul_assoc, hyu, hee]
    have h1 : b * (c - z • (1 : H →L[ℂ] H)) = e := by
      calc b * (c - z • (1 : H →L[ℂ] H)) = b * c - z • b := by rw [mul_sub, mul_smul_comm, mul_one]
        _ = b * c - z • (b * e) := by rw [hbe]
        _ = b * (c - z • e) := by rw [mul_sub, mul_smul_comm]
        _ = e := hbu
    have h2 : (1 - e) * (c - z • (1 : H →L[ℂ] H)) = -(z • (1 - e)) := by
      rw [sub_mul, one_mul, mul_sub, hec, mul_smul_comm, mul_one, smul_sub]
      abel
    have hL : (b - z⁻¹ • (1 - e)) * (c - z • (1 : H →L[ℂ] H)) = 1 := by
      rw [sub_mul, h1, smul_mul_assoc, h2, smul_neg, smul_smul, inv_mul_cancel₀ hz0, one_smul]
      abel
    set L := b - z⁻¹ • (1 - e) with hLd
    have hv : star (c - z • (1 : H →L[ℂ] H)) = c - z • 1 := by
      rw [star_sub, hcsa.star_eq, star_smul, hzr, star_one]
    have hR : (c - z • (1 : H →L[ℂ] H)) * star L = 1 := by
      have := congrArg star hL
      rwa [star_mul, hv, star_one] at this
    have hLR : L = star L := by
      calc L = L * ((c - z • (1 : H →L[ℂ] H)) * star L) := by rw [hR, mul_one]
        _ = star L := by rw [← mul_assoc, hL, one_mul]
    have hunit : IsUnit (c - z • (1 : H →L[ℂ] H)) := ⟨⟨c - z • 1, L, by rw [hLR]; exact hR, hL⟩, rfl⟩
    apply spectrum.mem_iff.mp hz
    rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
    exact hunit.neg
  let s : Set (Submodule ℂ (H →L[ℂ] H)) := {Z | Z ≤ Y ∧ (∀ a, ∀ x ∈ Z, π a * x ∈ Z) ∧ e ∉ Z}
  have hZ0 : Y.map (LinearMap.mulRight ℂ (c - z • e)) ∈ s := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      show y * (c - z • e) ∈ Y
      rw [mul_sub, mul_smul_comm, hYe y hy]
      exact Y.sub_mem (hYmul y hy c hcY) (Y.smul_mem z hy)
    · rintro a _ ⟨y, hy, rfl⟩
      exact ⟨π a * y, hY1 a y hy, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, hyu⟩
      exact hnotl y hy hyu
  obtain ⟨Y', hZY', hmax⟩ := zorn_le_nonempty₀ s (by
    intro C hCs hC Z0 hZ0C
    refine ⟨sSup C, ⟨sSup_le fun Z hZ => (hCs hZ).1, ?_, ?_⟩, fun Z hZ => le_sSup hZ⟩
    · intro a x hx
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp hx
      exact le_sSup hZ ((hCs hZ).2.1 a x hxZ)
    · intro he'
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp he'
      exact (hCs hZ).2.2 hxZ) _ hZ0
  obtain ⟨hY'Y, hY'G, heY'⟩ := hmax.prop
  have hY'E : ∀ x ∈ Y', e * x ∈ Y' := hE Y' hY'Y hY'G
  have hq := alt_quot K N hN π e hKe' hee Y Y' le_rfl heY hY1 hYE hSm hY'Y hY'G hY'E heY'
    (fun Z hZY hZG heZ hle => hmax.le_of_ge ⟨hZY, hZG, heZ⟩ hle) (n + 1) hd g
  rw [← hSdef, hSe] at hq
  have hcY' : c ∈ Y' := (hSZ Y' hY'Y hY'G S hq).2
  have huY' : c - z • e ∈ Y' := by
    have h := hZY' ⟨e, heY, rfl⟩
    have h' : (LinearMap.mulRight ℂ (c - z • e)) e = c - z • e := by
      rw [LinearMap.mulRight_apply, mul_sub, hec, mul_smul_comm, hee]
    rwa [h'] at h
  have hze : z • e ∈ Y' := by
    have := Y'.sub_mem hcY' huY'
    rwa [sub_sub_cancel] at this
  apply heY'
  have := Y'.smul_mem z⁻¹ hze
  rwa [smul_smul, inv_mul_cancel₀ hz0, one_smul] at this

end DiscreteGroups.sglob.LConv
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvBigC
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ} {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_entry_one (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  set r : Fin (m + 1) → k := fun j => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
    Matrix.of fun i j => if i = 0 then r j else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j
  have hMtri : ∀ i j : Fin (m + 1), j < i → M i j = 0 := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by subst e; exact (Fin.not_lt_zero j) hij
    simp [M, hi, Matrix.one_apply_ne hij.ne']
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa [M, r] using hg
    · simp [M, hi]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hMtri i j hij)]
    simp [hMdiag]
  set n : GL (Fin (m + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hnv : (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = M := rfl
  have hn : n ∈ unipB k (Fin (m + 1)) := (mem_unipB k).2 ⟨fun i j hij => by rw [hnv]; exact hMtri i j hij,
    fun i => by rw [hnv]; exact hMdiag i⟩
  have hwn : ∀ b, ((longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (Fin.last m) b = r b := by
    intro b
    rw [hnv, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (m + 1))]
    · rw [longElt_last, if_pos rfl, one_mul]
      simp [M, r]
    · intro a _ ha
      rw [longElt_last, if_neg ha, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set p : GL (Fin (m + 1)) k := longElt (m + 1) k * n * g
  have hP : IsP p := by
    intro j
    show ((longElt (m + 1) k * n * g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
    calc _ = ∑ b, r b * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) b j :=
          Finset.sum_congr rfl fun b _ => by rw [hwn b]
      _ = _ := by
        simp only [r]
        rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : g = n⁻¹ * (longElt (m + 1) k)⁻¹ * p := by
    simp only [p, mul_assoc, inv_mul_cancel_left]
  rw [hg', longElt_inv]
  simp only [map_mul, Module.End.mul_apply]
  rw [hl₁ _ (inv_mem hn), hl₂ _ (inv_mem hn), hW _ _ (agree_translate hl₁ hl₂ hX hP)]

theorem val_scalar (z : kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      Matrix.diagonal fun _ => (z : k) := by
  first
  | rfl
  | (ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply])

theorem agree_scalar {ω₁ ω₂ : kˣ →* ℂˣ} (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂)
    (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) (u : kˣ)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = u) :
    (ω₁ u : ℂ) * l₁ (π₁ g v₁) = (ω₂ u : ℂ) * l₂ (π₂ g v₂) := by
  have hent : (((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u * g)⁻¹ : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1 := by
    rw [mul_inv_rev, ← map_inv, Units.val_mul, val_scalar, Matrix.mul_diagonal, hg, Units.mul_inv]
  have := agree_of_entry_one hl₁ hl₂ hW hX _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₁, h₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at this

end DiscreteGroups.sglob.LConv

end
end

