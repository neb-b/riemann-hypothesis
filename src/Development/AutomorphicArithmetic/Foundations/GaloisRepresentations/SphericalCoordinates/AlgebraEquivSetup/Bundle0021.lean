module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDenom
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed.TensorDenominatorBound

open IsDedekindDomain.HeightOneSpectrum

variable {p : ℕ} [Fact p.Prime]

private def HasDen (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) : Prop :=
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ c • z ∈ LaHat D

private theorem HasDen.add {D : Datum p} {u w : AfP p ⊗[ℚ] VQ D} (hu : HasDen D u) (hw : HasDen D w) :
    HasDen D (u + w) := by
  obtain ⟨c, hc0, hcp, hc⟩ := hu
  obtain ⟨d, hd0, hdp, hd⟩ := hw
  refine ⟨c * d, Nat.mul_pos hc0 hd0, Nat.Coprime.mul_left hcp hdp, ?_⟩
  rw [smul_add]
  refine AddSubgroup.add_mem _ ?_ ?_
  · rw [mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ hc d
  · rw [mul_smul]
    exact AddSubgroup.nsmul_mem _ hd c

private theorem hasDen_zero (D : Datum p) : HasDen D 0 := by
  exact ⟨1, Nat.one_pos, Nat.coprime_one_left p, by simp [AddSubgroup.zero_mem]⟩

private theorem hasDen_gen (D : Datum p) (a : AfP p) (x : D.La) :
    HasDen D (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) := by
  obtain ⟨j, hj0, hjp, hj⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p a
  refine ⟨j, hj0, hjp, ?_⟩
  rw [TensorProduct.smul_tmul', nsmul_eq_mul]
  unfold LaHat
  exact AddSubgroup.subset_closure ⟨_, x, hj, rfl⟩

private theorem hasDen_tmul (D : Datum p) (a : AfP p) (t : VQ D) : HasDen D (a ⊗ₜ[ℚ] t) := by
  induction t using TensorProduct.induction_on with
  | zero => simpa using hasDen_zero D
  | tmul q x =>
    have e : (q ⊗ₜ[ℤ] x : VQ D) = q • ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    exact hasDen_gen D (q • a) x
  | add s t hs ht =>
    rw [TensorProduct.tmul_add]
    exact hs.add ht

private theorem hasDen (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) : HasDen D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact hasDen_zero D
  | tmul a t => exact hasDen_tmul D a t
  | add s t hs ht => exact hs.add ht

private noncomputable def inAfH (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D :=
  (TensorProduct.mk ℚ (AfP p) (VQ D) 1).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D.La 1).toAddMonoidHom

end UpperTheory.Gal.W2.Seed.TensorDenominatorBound

open UpperTheory.Gal.W2.Seed.TensorDenominatorBound in
theorem UpperTheory.Gal.W2.Seed.pDenom :
    Denom := by
  intro p _ D G L h
  haveI := D.finLa
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.La)
  choose c hc0 hcp hcm using fun x : D.La => hasDen D (L.actG h (inAfH D x))
  refine ⟨∏ x ∈ s, c x, Finset.prod_pos fun x _ => hc0 x,
    Nat.Coprime.prod_left fun x _ => hcp x, ?_⟩
  have hgen : ∀ x : D.La, (∏ y ∈ s, c y) • L.actG h (inAfH D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (s : Set D.La) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.mul_prod_erase s c hy, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ (hcm y) _
    | zero => simp [AddSubgroup.zero_mem]
    | add y z _ _ hy hz =>
      rw [map_add (f := _), map_add (f := _), smul_add]
      exact AddSubgroup.add_mem _ hy hz
    | smul n y _ hy =>
      rw [map_zsmul, map_zsmul, smul_comm]
      exact AddSubgroup.zsmul_mem _ hy n
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAfH D x := by
      simp [inAfH, TensorProduct.smul_tmul']
    rw [e, map_smul, smul_comm]
    exact GlobalTheory.W2.smul_mem_laHat ha (hgen x)
  | zero => simp [AddSubgroup.zero_mem]
  | add y z _ _ hy hz =>
    rw [map_add (f := _), smul_add]
    exact AddSubgroup.add_mem _ hy hz
  | neg y _ hy =>
    rw [map_neg, smul_neg]
    exact AddSubgroup.neg_mem _ hy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenActs
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pSeenActs :
    MemSum → MemAct → MemDeck → SeenShape → LevBasic → KNIdx → SeenActs := by
  intro hS hA hD hSh hLB _ E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen
  have hK : g.K ≤ Ty.kerK := (hSh E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen).1
  have hK₀ : Ty.K₀ = S.L.KN N.1 := hTy.K₀_eq
  have hker : Ty.kerK ≤ Ty.K := fun k hk => ((Ty.mem_kerK k).1 hk).1
  have hnorm : ∀ M : ℕ, ∀ k ∈ S.L.KN 1, ∀ u ∈ S.L.KN M, k * u * k⁻¹ ∈ S.L.KN M := fun M k hk u hu =>
    (hLB p S.D S.G S.L).2.2.2.2.1 _ _ ((hLB p S.D S.G S.L).2.2.1 M) k hk u hu
  have hnormK : ∀ k ∈ g.K, ∀ u ∈ S.L.KN g.M.1, k * u * k⁻¹ ∈ S.L.KN g.M.1 := fun k hk =>
    hnorm _ k (g.le_one hk)
  have hidx : (S.L.KN g.M.1).relIndex g.K ≠ 0 := fun h0 =>
    GlobalTheory.W2.relIndex_KN_ne_zero S.L one_pos (by have := g.M.2.1; omega) (Subgroup.relIndex_eq_zero_of_le_right g.le_one h0)
  refine ⟨fun a ha => ?_, fun hd hh => ?_, fun M' _ L' Kw t z hf hf' hap hz he => ?_⟩
  · obtain ⟨k, hk, hka⟩ := (hS _ g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h g.le hidx hnormK g.adm).2.1 a ha
    exact ⟨k, hker (hK hk), Ty.le (hK₀ ▸ hka)⟩
  · obtain ⟨h1, h2, h3⟩ := hd
    have := hD _ _ Ty Ty.kerK (Ty.triv_of_le le_rfl) g.h hh (fun u hu => by
      rw [hK₀] at hu ⊢; exact hnorm _ _ h3 u hu)
    rw [hK₀] at this
    have e : g.fn = memFn (S.L.KN N.1) (S.L.KN N.1) (S.L.KN N.1) g.h := by
      have : g.fn = memFn g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h := rfl
      rw [this, h1, h2]
    rw [e]; exact this
  · have := hA _ _ _ Ty L' Kw hf hap g.K (S.L.KN g.M.1) (Ty.triv_of_le hK) hf' (hK₀ ▸ g.le)
      (hK₀ ▸ KN_anti g.dvd) hidx hnormK t z g.h hz he (hK₀ ▸ g.adm)
    rw [hK₀, ← he] at this
    exact this
end

