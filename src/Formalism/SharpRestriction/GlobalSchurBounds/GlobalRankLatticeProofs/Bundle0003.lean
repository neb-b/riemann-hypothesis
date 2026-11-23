module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UnitaryKronecker
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneSevenOfFiniteOrder
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

section Gen

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K]

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs x hx y hy => hi ?_⟩
  exact TotallyDisconnectedSpace.isTotallyDisconnected_univ (f '' s) (Set.subset_univ _)
    (hs.image f hf.continuousOn) (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy)

theorem tens_finite :
    letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
    Module.Finite K (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  exact Module.Finite.equiv (R := K) (M := K ⊗[F] E) (N := E ⊗[F] K)
      { (TensorProduct.comm F K E) with
        map_smul' := fun c x => by
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a e =>
            simp [Algebra.smul_def, TensorProduct.smul_tmul']
            rw [show algebraMap K (E ⊗[F] K) c = (1 : E) ⊗ₜ[F] c from rfl,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          | add x y hx hy => simp_all [smul_add] }

theorem tens_topRing :
    letI := tensTop (F := F) (E := E) K
    IsTopologicalRing (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing K (E ⊗[F] K)

theorem tens_td [TotallyDisconnectedSpace K] :
    letI := tensTop (F := F) (E := E) K
    TotallyDisconnectedSpace (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  let e := (Module.finBasis K (E ⊗[F] K)).equivFun
  exact td_of_inj e (IsModuleTopology.continuous_of_linearMap e.toLinearMap) e.injective

end Gen

section Steps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {k : ℕ}

theorem inclE_injective (R : Type) [Field R] [Algebra F R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  exact (inclE (F := F) (E := E) R).injective

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (ι := Fin k) φ) := by
  intro x y hxy
  apply Units.ext
  ext i j
  have h := congrArg (fun z : GL (Fin k) B => (z : Matrix (Fin k) (Fin k) B) i j) hxy
  simpa [bc, hφ.eq_iff] using h

theorem bc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (x : GL (Fin k) A) : bc ψ (bc φ x) = bc (ψ.comp φ) x := by
  apply Units.ext
  ext i j
  simp [bc]

theorem prV_inclE [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) =
      inclE (F := F) (E := E) (v.adicCompletion F) := by
  ext x
  simp [prV, inclE]

theorem gl_topGroup {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    IsTopologicalGroup (GL (Fin k) T) := inferInstance

theorem gl_td {T : Type} [CommRing T] [TopologicalSpace T] [TotallyDisconnectedSpace T] :
    TotallyDisconnectedSpace (GL (Fin k) T) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin k) (Fin k) T) :=
    (inferInstance : TotallyDisconnectedSpace (Fin k → Fin k → T))
  exact td_of_inj (fun x : GL (Fin k) T => (x : Matrix (Fin k) (Fin k) T)) Units.continuous_val
    (fun a b hab => Units.ext hab)

theorem proG_order {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] (g : ℕ) (hg : g.Prime) (Uw : Subgroup G) (h : IsProG g Uw)
    (x : G) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) : ∃ m : ℕ, orderOf x = g ^ m := by
  classical
  obtain ⟨hc, hidx⟩ := h
  haveI : CompactSpace Uw := isCompact_iff_compactSpace.mp hc
  haveI : T1Space Uw := inferInstance
  let xu : Uw := ⟨x, hx⟩
  have hxu : orderOf xu = orderOf x := by
    exact Subgroup.orderOf_mk x hx
  have hnpos : 0 < orderOf x := hfin.orderOf_pos
  let Z : Finset Uw := (Finset.Ioo 0 (orderOf x)).image (fun j => xu ^ j)
  have hZ : IsOpen ((↑Z : Set Uw)ᶜ) := (Z.finite_toSet.isClosed).isOpen_compl
  have h1 : (1 : Uw) ∈ (↑Z : Set Uw)ᶜ := by
    intro hm
    obtain ⟨j, hj, hj1⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hm)
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.1 hj
    have := orderOf_le_of_pow_eq_one hj0 hj1
    omega
  obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup Uw, (N : Set Uw) ⊆ (↑Z : Set Uw)ᶜ := by
    haveI : T2Space Uw := inferInstance
    obtain ⟨H, hH⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := ProfiniteGrp.of Uw) hZ h1
    exact ⟨H, hH⟩
  haveI hNn : N.toSubgroup.Normal := N.isNormal'
  obtain ⟨m, hm⟩ := hidx N.toSubgroup N.isOpen' hNn
  have hpow : xu ^ (g ^ m) ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hm]
    exact pow_card_eq_one'
  have hdvd : orderOf x ∣ g ^ m := by
    by_contra hnd
    have hj0 : 0 < g ^ m % orderOf x :=
      Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have hjn : g ^ m % orderOf x < orderOf x := Nat.mod_lt _ hnpos
    have hmem : xu ^ (g ^ m % orderOf x) ∈ N.toSubgroup := by
      rw [← hxu, pow_mod_orderOf]
      exact hpow
    have hZm : xu ^ (g ^ m % orderOf x) ∈ (↑Z : Set Uw) :=
      Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, Finset.mem_Ioo.2 ⟨hj0, hjn⟩, rfl⟩)
    exact hN hmem hZm
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  exact ⟨i, hi⟩

theorem step_pro {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (g : ℕ) (hg : g.Prime) (Uw : Subgroup (GL (Fin k) T))
    (h : IsProG g Uw) (x : GL (Fin k) T) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) :
    ∃ m : ℕ, orderOf x = g ^ m := by
  haveI := gl_topGroup (k := k) (T := T)
  haveI := gl_td (k := k) (T := T)
  exact proG_order g hg Uw h x hx hfin

end Steps

def DefiniteUnitaryFiniteOrder (D : D7) : Prop :=
  ∀ σ : D.host.E →ₐ[D.host.F] D.host.E, (∀ x, σ x = D.host.conj x) →
  ∀ J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E, IsHerm (σ : D.host.E →+* D.host.E) J → IsDef σ J →
  letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  ∀ U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
  ∀ γ ∈ UJ (σ : D.host.E →+* D.host.E) J,
    bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∈
      U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

set_option maxHeartbeats 1000000 in
theorem finiteModel_of_heckeEstimate (D : D7) (hF : DefiniteUnitaryFiniteOrder D) : division_rows_rational_lattice D := by
  intro σ hσ J hJ hD g hg hlt v hv U hU hUc _hUo Uw hUw hUUw y hy
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx1
  have hfin : IsOfFinOrder γ := hF σ hσ J hJ hD U hU hUc y hy γ hγ hx2
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx2
  have hcomp : bc (prV v) (bc (inclE (F := D.host.F) (E := D.host.E)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ) =
      bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ := by
    rw [bc_comp, prV_inclE]
  have hordγ : orderOf (bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ)
      = orderOf γ :=
    orderOf_injective (bc (ι := Fin D.R.k) (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)))
      (bc_injective _ (inclE_injective (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))) γ
  have hconj : bc (prV v) ((MulAut.conj y).toMonoidHom u) =
      MulAut.conj (bc (prV v) y) (bc (prV v) u) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hord_u : orderOf (bc (prV v) u) = orderOf γ := by
    have e1 := MulEquiv.orderOf_eq (MulAut.conj (bc (prV v) y)) (bc (prV v) u)
    have e2 := congrArg (fun z => orderOf (bc (prV v) z)) hux
    have e3 := congrArg orderOf hcomp
    rw [← e1, ← hconj, e2, e3, hordγ]
  have hfin' : IsOfFinOrder (bc (prV v) u) := by
    rw [← orderOf_pos_iff, hord_u]
    exact hfin.orderOf_pos
  obtain ⟨m, hm⟩ := @step_pro D.R.k _ _
    (tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))
    (tens_topRing (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    (tens_td (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    g hg Uw hUw (bc (prV v) u) (hUUw u hu) hfin'
  rw [hord_u] at hm
  have hlt' : 4 * D.R.ord * D.R.k < g - 1 := by
    have h2 : 2 * D.R.f * D.R.k = 4 * D.R.ord * D.R.k := by
      have hf : D.R.f = 2 * D.R.ord := rfl
      rw [hf]
      ring
    omega
  have hΓ := Formalism.HC.HostAx.hostStab D.host.toHostAx D.R.k g hg hlt' (Subgroup.zpowers γ) (by
      intro δ hδ
      have hd : orderOf δ ∣ g ^ m := hm ▸ orderOf_dvd_of_mem_zpowers hδ
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hd
      exact ⟨i, hi⟩)
  have h1 : γ = 1 := by
    have hm' : γ ∈ Subgroup.zpowers γ := Subgroup.mem_zpowers γ
    rw [hΓ] at hm'
    exact Subgroup.mem_bot.mp hm'
  rw [h1, map_one]

theorem totReal_emb {F : Type} [Field F] [IsTotallyReal F] (φ : F →+* ℂ) :
    ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ) := by
  have h : NumberField.ComplexEmbedding.IsReal φ := by
    exact NumberField.IsTotallyReal.complexEmbedding_isReal φ
  exact ⟨h.embedding, fun x => (h.coe_embedding_apply x).symm⟩

theorem finite_order_of_totally_real (hG : Formalism.MainNotions.Ext.FinOrdG) (D : D7) : DefiniteUnitaryFiniteOrder D := by
  intro σ _ J hJ hD U hU hUc y hy γ hγ hmem
  exact hG D.host.F D.host.E (fun φ => totReal_emb φ) σ D.R.k J hJ hD U hU hUc y hy γ hγ hmem

end Formalism.MainNotions.UnusedSlot33
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

def InertPart (D : D7) : Prop :=
  ∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ h : HH D,
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 →
      frob D p = gOf D φ₀ h →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ φ₀ = c0 ∧ Odd (addOrderOf h)))

theorem tau_one_mem_orbit_set (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.chD (φ.tau1 t) = 1
  rfl

private theorem neg_one_of_ne {x : ℤˣ} (h : x ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · exact absurd hx h
  · exact hx

private theorem no_three (R : Formalism.HC.Frame) {L : ℕ} (T : Finset ℕ) (hTr : ∀ s ∈ T, 4 * L * s < R.n0)
    (hTn : NoRel T L) (u0 : R.A) (hL : 3 ≤ L) (φ : R.GG) (hφ : φ ∉ R.Psi) (hφc : φ ≠ R.cc)
    (τ : R.GG) (hτ : τ ∈ R.Psi) (i : ℕ)
    (h0 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ i * τ) = R.tau2 (R.dig s + u0))
    (h1 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) = R.tau2 (R.dig s + u0))
    (h2 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) = R.tau2 (R.dig s + u0)) : False := by
  have key : ∀ (y : R.GG), (Formalism.HC.Frame.placeOf y).1.1 = -1 →
      (Formalism.HC.Frame.placeOf (φ * y)).1.1 = -1 → φ.1.1 = -1 := by
    intro y h0 h1
    have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
    simp only [Formalism.HC.Frame.placeOf] at h0 h1
    rcases Int.units_eq_one_or y.1.2 with hy | hy
    · rw [if_pos hy] at h0
      have hm : (φ * y).1.2 = -1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_neg (by rw [hm]; decide)] at h1
      simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul, h0] using h1
    · rw [if_neg (by rw [hy]; decide)] at h0
      have hm : (φ * y).1.2 = 1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_pos hm] at h1
      have h0' : y.1.1 = 1 := by
        simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul] using h0
      simpa [Prod.fst_mul, h0'] using h1
  have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
  obtain ⟨s1, hs1, e1⟩ := h0
  obtain ⟨s2, hs2, e2⟩ := h1
  obtain ⟨s3, hs3, e3⟩ := h2
  have hφ1 : φ.1.1 = -1 := key (φ ^ i * τ) (by rw [e1]; rfl)
    (by rw [← mul_assoc, ← pow_succ', e2]; rfl)
  have E : ∀ (k s : ℕ), Formalism.HC.Frame.placeOf (φ ^ k * τ) = R.tau2 (R.dig s + u0) →
      k • R.iotaInv φ.2 + R.iotaInv τ.2 = R.dig s + u0 := by
    intro k s hk
    have this : R.iotaInv (Formalism.HC.Frame.placeOf (φ ^ k * τ)).2 = R.iotaInv (R.tau2 (R.dig s + u0)).2 := by
      rw [hk]
    rw [Formalism.HC.Frame.placeOf_snd, Prod.snd_mul, Prod.pow_snd, Formalism.HC.Frame.iotaInv_mul,
      Formalism.HC.Frame.iotaInv_pow] at this
    change _ = R.iotaInv (R.iota _) at this
    rw [Formalism.HC.Frame.iotaInv_iota] at this
    exact this
  have E1 := E i s1 e1
  have E2 := E (i + 1) s2 e2
  have E3 := E (i + 2) s3 e3
  set x := R.iotaInv φ.2 with hxdef
  set T0 := R.iotaInv τ.2
  have hx1 : R.dig s2 - R.dig s1 = x := by
    have a : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    have b : R.dig s1 = (i • x + T0) - u0 := by rw [E1]; abel
    rw [a, b, succ_nsmul]
    abel
  have hx2 : R.dig s3 - R.dig s2 = x := by
    have a : R.dig s3 = ((i + 2) • x + T0) - u0 := by rw [E3]; abel
    have b : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    rw [a, b, show i + 2 = (i + 1) + 1 from rfl, succ_nsmul]
    abel
  have hx0 : x ≠ 0 := by
    intro h0
    apply hφc
    have h2 : φ.2 = 1 := (R.iotaInv_eq_zero_iff _).1 h0
    exact Prod.ext (Prod.ext hφ1 hφ2) h2
  have hzero : ((s1 : ℤ) + s3 - s2 - s2) • R.a0 = 0 := by
    rw [sub_zsmul, sub_zsmul, add_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
    change R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = 0
    have : R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 =
        (R.dig s3 - R.dig s2) - (R.dig s2 - R.dig s1) := by abel
    rw [this, hx1, hx2, sub_self]
  have hdvd : (R.n0 : ℤ) ∣ (s1 : ℤ) + s3 - s2 - s2 := addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero
  have b1 := hTr s1 hs1
  have b2 := hTr s2 hs2
  have b3 := hTr s3 hs3
  have c1 : 12 * s1 ≤ 4 * L * s1 := Nat.mul_le_mul_right s1 (by omega)
  have c2 : 12 * s2 ≤ 4 * L * s2 := Nat.mul_le_mul_right s2 (by omega)
  have c3 : 12 * s3 ≤ 4 * L * s3 := Nat.mul_le_mul_right s3 (by omega)
  have habs : |(s1 : ℤ) + s3 - s2 - s2| < R.n0 := abs_lt.2 ⟨by omega, by omega⟩
  have hrel : (s1 : ℤ) + s3 - s2 - s2 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have n12 : s1 ≠ s2 := by
    rintro rfl
    exact hx0 (by rw [← hx1, sub_self])
  have n23 : s2 ≠ s3 := by
    rintro rfl
    exact hx0 (by rw [← hx2, sub_self])
  have n13 : s1 ≠ s3 := by
    rintro rfl
    apply n12
    omega
  apply hTn s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 1 2 (by norm_num) (by norm_num; omega) (by norm_num)
    (by norm_num; omega) (by norm_num)
  linarith

theorem even_addOrderOf_of_h_ne_zero (D : D7) {h : D.R.A} (hh : D.R.h h ≠ 0) : Even (addOrderOf h) := by
  have h1 : addOrderOf (D.R.h h) ∣ addOrderOf h := addOrderOf_map_dvd D.R.h h
  have h2 : addOrderOf (D.R.h h) ∣ 2 ^ D.R.e := by
    have := D.R.orderOf_H_dvd (Additive.toMul (D.R.h h))
    rwa [← addOrderOf_ofMul_eq_orderOf, ofMul_toMul] at this
  have h3 : addOrderOf (D.R.h h) ≠ 1 := by
    intro hx
    apply hh
    have := addOrderOf_nsmul_eq_zero (D.R.h h)
    rwa [hx, one_nsmul] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h3 (by simpa using hk')
  rw [even_iff_two_dvd]
  refine dvd_trans ?_ h1
  rw [hk']
  exact dvd_pow_self 2 hk0

theorem cc_mem_zpowers_gOf (D : D7) (φ₀ : G0) (h : HH D) :
    D.R.cc ∈ Subgroup.zpowers (gOf D φ₀ h) ↔ φ₀ = c0 ∧ Odd (addOrderOf h) := by
  have hu : ∀ (u : ℤˣ) (k : ℤ), u ^ k = -1 → u = -1 ∧ Odd k := by
    intro u k huk
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [one_zpow] at huk
      exact absurd huk (by decide)
    · refine ⟨rfl, ?_⟩
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow] at huk
        exact absurd huk (by decide)
      · exact ho
  have hc0sq : c0 ^ 2 = 1 := by
    ext <;> simp [c0]
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    have e1 : φ₀ ^ k = c0 := congrArg Prod.fst hk
    have e2 : (Multiplicative.ofAdd h) ^ k = 1 := congrArg Prod.snd hk
    have e2' : k • h = 0 := by
      have := congrArg Multiplicative.toAdd e2
      simpa using this
    have a1 := hu _ _ (congrArg Prod.fst e1)
    have a2 := hu _ _ (congrArg Prod.snd e1)
    refine ⟨Prod.ext a1.1 a2.1, ?_⟩
    have hd : (addOrderOf h : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.2 e2'
    have hd' : addOrderOf h ∣ k.natAbs := Int.natCast_dvd.1 hd
    exact Odd.of_dvd_nat (Int.natAbs_odd.2 a1.2) hd'
  · rintro ⟨rfl, hodd⟩
    refine ⟨(addOrderOf h : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · change c0 ^ ((addOrderOf h : ℕ) : ℤ) = c0
      rw [zpow_natCast]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hc0sq, one_pow, one_mul]
    · change (Multiplicative.ofAdd h) ^ ((addOrderOf h : ℕ) : ℤ) = 1
      rw [zpow_natCast, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero]

theorem lemma_one_three_of_inert (D : D7) (hI : InertPart D) : PointsLemma D := by
  intro φ₀ hφ₀ h
  have hg1 : (gOf D φ₀ h).1 = φ₀ := rfl
  have hsg : sgc0 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    ext <;> simp [sgc0, c0]
  have hg : (gOf D φ₀ h).1 = c0 ∨ (gOf D φ₀ h).1 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    rw [hg1, ← hsg]
    exact hφ₀
  have hchg : D.R.chD (gOf D φ₀ h) = -1 := by
    change φ₀.2 = -1
    rcases hφ₀ with rfl | rfl
    · rfl
    · rw [hsg]
  have hcc : D.R.chD D.R.cc = -1 := rfl
  refine ⟨?_, ?_, ?_, ?_, cc_mem_zpowers_gOf D φ₀ h, hI φ₀ hφ₀ h, ?_⟩
  · intro τ hτ i
    have hτ' : D.R.chD τ = 1 := hτ
    constructor
    · intro he
      show D.R.chD _ = 1
      rw [map_mul, map_pow, hchg, hτ', he.neg_one_pow, one_mul]
    · intro ho
      refine ⟨D.R.cc * ((gOf D φ₀ h) ^ i * τ), ?_, ?_⟩
      · show D.R.chD _ = 1
        rw [map_mul, map_mul, map_pow, hchg, hτ', ho.neg_one_pow, hcc]
        decide
      · rw [← mul_assoc, cc_mul_cc, one_mul]
  · intro t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).1
    show D.R.iotaInv (Formalism.HC.Frame.placeOf _).2 = _
    rw [this, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]
    change i • D.R.iotaInv (D.R.iota h) + D.R.iotaInv (D.R.iota t) = t + i • h
    rw [Formalism.HC.Frame.iotaInv_iota, Formalism.HC.Frame.iotaInv_iota, add_comm]
  · intro hc t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.1
      (by rw [hg1]; exact hc)
    rw [this]
    rfl
  · intro hs t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.2
      (by rw [hg1, hs, hsg])
    rw [this]
    exact mul_one _
  · intro hc τ hτ
    refine ⟨?_, even_addOrderOf_of_h_ne_zero D⟩
    rw [Formalism.HC.Frame.hostOrbitCount (φ := D.R.toFrame) _ (by rw [hg1]; exact hc) τ hτ]
    exact orderOf_ofAdd_eq_addOrderOf h

theorem no_three_consecutive_thick_places (D : D7) : TorusPairsWithVariant D := by
  intro hL φ hφ hφc τ hτ i ⟨h0, h1, h2⟩
  have mem : ∀ g : D.R.GG, g ∈ thick D → ∃ s ∈ D.host.T2, g = D.R.tau2 (D.R.dig s + D.host.u0) := by
    intro g hg
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hg
    exact ⟨s, hs, he.symm⟩
  exact no_three D.R.toFrame D.host.T2 D.host.second_set_range D.host.second_set_no_relation D.host.u0 hL φ hφ hφc τ hτ i
    (mem _ h0) (mem _ h1) (mem _ h2)

end Formalism.MainNotions.UnusedSlot33

end
end

