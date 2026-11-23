module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section Mean

open GroundTheory.Automorphic (stabilizerOf mem_stabilizerOf)

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private noncomputable def mean (T : Subgroup H) [T.FiniteIndex] (v : V) : V :=
  (Nat.card (H ⧸ T) : ℂ)⁻¹ • ∑ q : H ⧸ T, ρ q.out v

private theorem card_ne (T : Subgroup H) [T.FiniteIndex] : (Nat.card (H ⧸ T) : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Subgroup.FiniteIndex.index_ne_zero

private theorem out_apply {T : Subgroup H} {v : V} (hv : ∀ t ∈ T, ρ t v = v) (x : H) :
    ρ (x : H ⧸ T).out v = ρ x v := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T x
  rw [ht, map_mul, Module.End.mul_apply, hv t t.2]

private theorem mean_eq {T' T : Subgroup H} [T'.FiniteIndex] [T.FiniteIndex] (hle : T' ≤ T) {v : V}
    (hv : ∀ t ∈ T, ρ t v = v) : mean ρ T' v = mean ρ T v := by
  unfold mean
  have hcard : Nat.card (H ⧸ T') = Nat.card (H ⧸ T) * Nat.card (T ⧸ T'.subgroupOf T) := by
    rw [Nat.card_congr (Subgroup.quotientEquivProdOfLE hle), Nat.card_prod]
  have hsum : ∑ q : H ⧸ T', ρ q.out v =
      ∑ x : (H ⧸ T) × (T ⧸ T'.subgroupOf T), ρ x.1.out v := by
    refine Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ _ ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.quotientEquivProdOfLE_apply]
    show ρ (x : H ⧸ T').out v = ρ (x : H ⧸ T).out v
    rw [out_apply ρ (fun t ht => hv t (hle ht)), out_apply ρ hv]
  have hm : (Nat.card (T ⧸ T'.subgroupOf T) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [hsum, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]

private theorem mean_mem {T : Subgroup H} [T.FiniteIndex] {v : V} (hv : ∀ t ∈ T, ρ t v = v) (h : H) :
    ρ h (mean ρ T v) = mean ρ T v := by
  unfold mean
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((h * q.out : H) : H ⧸ T) = h • q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (h * q.out), hq]
  rfl

private theorem mean_lin {W : Type} [AddCommGroup W] [Module ℂ W] (T : Subgroup H) [T.FiniteIndex]
    (p : V →ₗ[ℂ] W) {v : V} (hp : ∀ h, p (ρ h v) = p v) : p (mean ρ T v) = p v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mean, map_smul, map_sum, hp, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne T), one_smul]

private theorem mean_add (T : Subgroup H) [T.FiniteIndex] (x y : V) :
    mean ρ T (x + y) = mean ρ T x + mean ρ T y := by
  simp only [mean, map_add (f := _), Finset.sum_add_distrib, smul_add]

private theorem mean_smul (T : Subgroup H) [T.FiniteIndex] (c : ℂ) (x : V) :
    mean ρ T (c • x) = c • mean ρ T x := by
  simp only [mean, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem mean_act {T : Subgroup H} [T.FiniteIndex] [T.Normal] {v : V} (hv : ∀ t ∈ T, ρ t v = v)
    (h : H) : mean ρ T (ρ h v) = mean ρ T v := by
  unfold mean
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight (h : H ⧸ T)) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((q.out * h : H) : H ⧸ T) = q * (h : H ⧸ T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (q.out * h), hq]
  rfl

private theorem exists_avg (hfin : ∀ v, (stabilizerOf ρ v).FiniteIndex) : ∃ e : V →ₗ[ℂ] V,
    (∀ h v, ρ h (e v) = e v) ∧ (∀ h v, e (ρ h v) = e v) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V),
        (∀ h, p (ρ h v) = p v) → p (e v) = p v := by
  let E : V → V := fun v => @mean H V _ _ _ ρ (stabilizerOf ρ v) (hfin v) v
  have hE : ∀ (v : V) (T : Subgroup H) [T.FiniteIndex], T ≤ stabilizerOf ρ v → E v = mean ρ T v := by
    intro v T _ hle
    haveI := hfin v
    exact (mean_eq ρ hle (fun t ht => mem_stabilizerOf.1 ht)).symm
  have hfx : ∀ v, ∀ t ∈ stabilizerOf ρ v, ρ t v = v := fun v t ht => mem_stabilizerOf.1 ht
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    haveI := hfin x
    haveI := hfin y
    haveI := hfin (x + y)
    show E (x + y) = E x + E y
    rw [hE (x + y) (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_left),
      hE y (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_right),
      mean_add]
  · intro c x
    haveI := hfin x
    haveI := hfin (c • x)
    show E (c • x) = c • E x
    rw [hE (c • x) (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_left, mean_smul]
  · intro h v
    haveI := hfin v
    exact mean_mem ρ (hfx v) h
  · intro h v
    haveI := hfin v
    haveI := hfin (ρ h v)
    have hle : (stabilizerOf ρ v).normalCore ≤ stabilizerOf ρ (ρ h v) := by
      intro t ht
      rw [mem_stabilizerOf]
      have h1 : h⁻¹ * t * h ∈ (stabilizerOf ρ v).normalCore := by
        have := (Subgroup.normalCore_normal (stabilizerOf ρ v)).conj_mem t ht h⁻¹
        simpa using this
      have h2 := hfx v _ (Subgroup.normalCore_le _ h1)
      calc ρ t (ρ h v) = ρ (t * h) v := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (h * (h⁻¹ * t * h)) v := by rw [show h * (h⁻¹ * t * h) = t * h by group]
        _ = ρ h (ρ (h⁻¹ * t * h) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ h v := by rw [h2]
    show E (ρ h v) = E v
    rw [hE (ρ h v) _ hle, hE v _ (Subgroup.normalCore_le _),
      mean_act ρ (fun t ht => hfx v t (Subgroup.normalCore_le _ ht)) h]
  · intro W _ _ p v hp
    haveI := hfin v
    exact mean_lin ρ _ p hp

end Mean

theorem UpperTheory.Gal.Join.avgEx :
    UpperTheory.Gal.Join.AvgEx := by
  intro G V _ _ _ _ _ π hsm K hK
  unfold IsSmooth at hsm
  unfold CO at hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  let ρ : Representation ℂ K V := π.comp K.subtype
  have hfin : ∀ v, (GroundTheory.Automorphic.stabilizerOf ρ v).FiniteIndex := by
    intro v
    haveI := Subgroup.quotient_finite_of_isOpen (GroundTheory.Automorphic.stabilizerOf ρ v) ((hsm v).preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨e, he1, he2, he3⟩ := exists_avg ρ hfin
  have hfix : ∀ w, (∀ g ∈ K, π g w = w) → e w = w := by
    intro w hw
    have := he3 V LinearMap.id w (fun h => hw h h.2)
    simpa using this
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro g hg
    exact he1 ⟨g, hg⟩ v
  · intro v hv
    rw [GlobalTheory.Parabolic.mem_fixed] at hv
    exact hfix v hv
  · intro g hg v
    exact he2 ⟨g, hg⟩ v
  · intro W _ _ p v hp
    exact he3 W p v (fun h => hp h h.2)
  · intro s A hA hs hsurj v
    have h1 : e (A (e v)) = A (e v) := by
      apply hfix
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hsurj g hg
      rw [← hA]
      congr 1
      exact he1 ⟨h, hh⟩ v
    have h2 : e (A (e v)) = e (A v) := by
      refine he3 V (e ∘ₗ A) v (fun h => ?_)
      show e (A (π h v)) = e (A v)
      rw [hA]
      exact he2 ⟨s h, hs h h.2⟩ (A v)
    rw [← h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpLev
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.expLev :
    UpperTheory.Gal.Join.ExpLev := by
  intro k _ _ _ _ n V _ _ π hs y
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  let U : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  refine ⟨U, hs v, fun K hK => ?_⟩
  refine Submodule.mem_map_of_mem (p := fixed π K) ?_
  intro h
  have hv : π (h : GL (Fin n) k) v = v := hK h.2
  simpa using hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.HeckeMul
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem rep_mul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (w : V) : π (a * b) w = π a (π b w) := by
  rw [map_mul, Module.End.mul_apply]

private theorem exists_unipotent_eq_of_mem_iwLev_of_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (K : Subgroup (GL (Fin n) k)) (hK : IwLev K) (t : Fin n → kˣ) (ht : Dom t) (v : V)
    (hv : v ∈ fixed π K) (g : GL (Fin n) k) (hg : g ∈ K) :
    ∃ u ∈ K ⊓ unipB k (Fin n),
      π g (π (diagT k (Fin n) t) v) = π u (π (diagT k (Fin n) t) v) := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact g hg
  refine ⟨u, hu, ?_⟩
  have h1 : ∀ x : K, π x v = ((1 : K →* ℂˣ) x : ℂ) • v := hv
  have hfix : ∀ h ∈ K, π h v = v := fun h hh => by simpa using h1 ⟨h, hh⟩
  have hc' := hK.low t ht c hc
  have hcomm : diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : u * diagT k (Fin n) d * c * diagT k (Fin n) t =
      u * diagT k (Fin n) t * (diagT k (Fin n) d *
        ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t)) := by
    calc u * diagT k (Fin n) d * c * diagT k (Fin n) t
        = u * (diagT k (Fin n) d * diagT k (Fin n) t) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by group
      _ = u * (diagT k (Fin n) t * diagT k (Fin n) d) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by rw [hcomm]
      _ = _ := by group
  rw [← rep_mul π (u * diagT k (Fin n) d * c), key, rep_mul π (u * diagT k (Fin n) t),
    rep_mul π (diagT k (Fin n) d), hfix _ hc', hfix _ hd, rep_mul]

theorem UpperTheory.Gal.Join.heckeMul :
    UpperTheory.Gal.Join.HeckeMul := by
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π K hK e he t ht v hv
  have hN : ∀ u ∈ K ⊓ unipB k (Fin n), ∀ w : V,
      (twKer π (unipB k (Fin n)) 1).mkQ (π u w) = (twKer π (unipB k (Fin n)) 1).mkQ w := by
    intro u hu w
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨u, (Subgroup.mem_inf.mp hu).2⟩, w, by simp⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · have h2 := he.lin V (e.comp (π (diagT k (Fin n) s))) (π (diagT k (Fin n) t) v) ?_
    · simp only [LinearMap.comp_apply] at h2
      rw [h2, map_mul, rep_mul]
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      simp only [LinearMap.comp_apply]
      rw [hgu, ← rep_mul π (diagT k (Fin n) s) u,
        show diagT k (Fin n) s * u =
          (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹) * diagT k (Fin n) s by group,
        rep_mul π (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹),
        he.inv _ (hK.up s hs u hu)]
  · have h3 := he.lin _ (twKer π (unipB k (Fin n)) 1).mkQ (π (diagT k (Fin n) t) v) ?_
    · exact h3.trans rfl
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      rw [hgu, hN u hu]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.JacNorm
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.jacNorm :
    UpperTheory.Gal.Join.JacNorm := by
  intro k _ _ _ _ n V _ _ π t y
  rw [UnramFixed.jacB_apply, smul_smul]
  have h1 : ((((deltaHalf k fun _ : Fin n ↦ Unit).comp (leviTorus k (Fin n)).toMonoidHom) t : ℂˣ) : ℂ) =
      ((√(deltaB t) : ℝ) : ℂ) := by
    rw [MonoidHom.comp_apply, val_deltaHalf, deltaB_eq_modulus]
    rfl
  have h2 : ((√(deltaB t) : ℝ) : ℂ) ≠ 0 := by
    rw [← h1]
    exact Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, h1, mul_inv_cancel₀ h2, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.KerKill
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join.KernelKilling

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  have hinv : (((diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => ((t i : k))⁻¹ := by
    rw [← map_inv, val_diagT]
    congr 1
    funext i
    simp
  rw [Units.val_mul, Units.val_mul, hinv, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_close {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    {c B : ValueGroupWithZero k} (hc : c ≤ 1) (hB0 : B ≠ 0)
    (hB : ∀ i j, valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B)
    (t : Fin n → kˣ)
    (ht : ∀ i j, i < j → valuation k (t i : k) ≤ c * B⁻¹ * valuation k (t j : k)) (i j : Fin n) :
    valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ c ∧
      valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  rw [conj_entry]
  rw [mem_unipB] at hu
  obtain ⟨hlow, hdiag⟩ := hu
  have hc1 : c ≤ 1 := hc
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hne : i ≠ j := ne_of_lt hij
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne hne
    have hvj : valuation k (t j : k) ≠ 0 := by simp
    have key : valuation k ((t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹) ≤ c := by
      rw [map_mul, map_mul, map_inv₀]
      calc valuation k (t i : k) * valuation k ((u : Matrix (Fin n) (Fin n) k) i j) *
            (valuation k (t j : k))⁻¹
          ≤ c * B⁻¹ * valuation k (t j : k) * B * (valuation k (t j : k))⁻¹ := by
            gcongr
            · exact ht i j hij
            · exact hB i j
        _ = c * (B⁻¹ * B) * (valuation k (t j : k) * (valuation k (t j : k))⁻¹) := by
            simp only [mul_comm, mul_assoc, mul_left_comm]
        _ = c := by rw [inv_mul_cancel₀ hB0, mul_inv_cancel₀ hvj, mul_one, mul_one]
    rw [h1, sub_zero]
    exact ⟨key, le_trans key hc1⟩
  · rw [hdiag i, Matrix.one_apply_eq]
    have : (t i : k) * 1 * (t i : k)⁻¹ = 1 := by simp
    rw [this, sub_self, map_zero, map_one]
    exact ⟨zero_le', le_refl _⟩
  · have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    rw [hlow i j hij, h1]
    simp

private theorem exists_bound (u : GL (Fin n) k) : ∃ B : ValueGroupWithZero k, B ≠ 0 ∧ ∀ i j,
    valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B ∧
      valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ B := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : Fin n × Fin n =>
    max (valuation k ((u : Matrix (Fin n) (Fin n) k) p.1 p.2))
      (valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2)))
  refine ⟨max M 1, ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  · exact le_trans (le_trans (le_max_left _ _) (hM (i, j))) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) (hM (i, j))) (le_max_left _ _)

private theorem conj_mem {K : Subgroup (GL (Fin n) k)} (hK : IsOpen (K : Set (GL (Fin n) k)))
    {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) :
    ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
      (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) →
        diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ K := by
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1
    (hK.mem_nhds K.one_mem)
  obtain ⟨B, hB0, hB⟩ := exists_bound u
  set c : ValueGroupWithZero k :=
    valuation k ((GroundTheory.Automorphic.GLnLocal.uniformizer k : k)) ^ m with hcdef
  have hc : c ≤ 1 := pow_le_one₀ zero_le'
    (le_of_lt (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k))
  have hc0 : c ≠ 0 := pow_ne_zero _ (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)
  have hui : u⁻¹ ∈ unipB k (Fin n) := inv_mem hu
  refine ⟨c * B⁻¹, mul_ne_zero hc0 (inv_ne_zero hB0), fun t ht => hm ?_⟩
  have hA := conj_close hu hc hB0 (fun i j => (hB i j).1) t ht
  have hI := conj_close hui hc hB0 (fun i j => (hB i j).2) t ht
  have hinv : (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹)⁻¹ =
      diagT k (Fin n) t * u⁻¹ * (diagT k (Fin n) t)⁻¹ := by group
  rw [SetLike.mem_coe, GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff,
    GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, hinv]
  refine ⟨⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hA i j).2,
    fun i j => (Valuation.mem_integer_iff _ _).2 (hI i j).2⟩, fun i j => (hA i j).1⟩

end UpperTheory.Gal.Join.KernelKilling

theorem UpperTheory.Gal.Join.kerKill :
    UpperTheory.Gal.Join.KerKill := by
  intro k _ _ _ _ n V _ _ π K hK e he v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, x, rfl⟩ := hw
    obtain ⟨r, hr, h⟩ := UpperTheory.Gal.Join.KernelKilling.conj_mem hK.co.2 u.2
    refine ⟨r, hr, fun t ht => ?_⟩
    have hk := he.inv _ (h t ht) (π (diagT k (Fin n) t) x)
    have hc : π (diagT k (Fin n) t * (u : GL (Fin n) k) * (diagT k (Fin n) t)⁻¹)
        (π (diagT k (Fin n) t) x) = π (diagT k (Fin n) t) (π (u : GL (Fin n) k) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [hc] at hk
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hk, sub_self]
  | zero => exact ⟨1, one_ne_zero, fun t _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r₁, h₁, ha⟩ := ha
    obtain ⟨r₂, h₂, hb⟩ := hb
    refine ⟨min r₁ r₂, ?_, fun t ht => ?_⟩
    · rcases min_choice r₁ r₂ with h | h <;> rw [h] <;> assumption
    · rw [map_add (f := _), map_add (f := _),
        ha t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_left _ _) le_rfl),
        hb t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_right _ _) le_rfl), add_zero]
  | smul c a _ ha =>
    obtain ⟨r, hr, ha⟩ := ha
    exact ⟨r, hr, fun t ht => by rw [map_smul, map_smul, ha t ht, smul_zero]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.NormDom
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.normDom :
    UpperTheory.Gal.Join.NormDom := by
  intro k k' _ _ _ _ _ _ _ _ ι σ l N hN
  refine ⟨fun x => ?_, fun n t => ⟨fun ht i j hij => ?_, ?_, fun s ht hs i j hij => ?_⟩⟩
  · apply Units.ext
    apply ι.injective
    rw [hN.prod, hN.prod]
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := hN.cyc.pos; omega⟩
    subst hm
    have hord : σ^[m + 1] (x : k') = x := hN.cyc.ord x
    have hl : ∀ i, σ^[i] ((Units.map (σ : k' →* k') x : k'ˣ) : k') = σ^[i + 1] (x : k') := fun i => by
      rw [Function.iterate_succ_apply]
      rfl
    simp only [hl]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => σ^[i] (x : k')), hord]
    rfl
  · refine lt_of_not_ge fun h => ?_
    have h1 := (GlobalTheory.SplitWeil.nabs_le_iff (N (t j)) (N (t i))).2 h
    rw [hN.abs, hN.abs] at h1
    exact absurd h1 (not_le.2 (GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt (ht i j hij)))
  · unfold deltaB
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    have e : nT n N t i / nT n N t j = N (t i / t j) := by
      rw [map_div]
      rfl
    rw [e, hN.abs]
  · have hj : valuation k' (s j : k') ≠ 0 := by simp
    have e : ∀ a, valuation k' (((t * s) a : k'ˣ) : k') = valuation k' (t a : k') * valuation k' (s a : k') := fun a => by
      simp
    rw [e, e]
    calc valuation k' (t i : k') * valuation k' (s i : k')
        ≤ valuation k' (t i : k') * valuation k' (s j : k') := mul_le_mul' le_rfl (hs i j hij)
      _ < valuation k' (t j : k') * valuation k' (s j : k') :=
        mul_lt_mul_of_pos_right (ht i j hij) (zero_lt_iff.2 hj)
end

