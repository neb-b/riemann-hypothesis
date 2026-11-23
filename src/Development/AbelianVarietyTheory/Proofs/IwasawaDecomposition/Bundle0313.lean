module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
section
noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

@[reducible] def algK (D : D7) (jE : D.host.E →+* Qb) {M : Fld} (h : KQbar D jE ≤ M) : Algebra D.host.K M :=
  ((IntermediateField.inclusion h).toRingHom.comp (D.host.K.equivMap jE.toRatAlgHom).toRingHom).toAlgebra

theorem nfOf {M : Fld} (h : FiniteDimensional ℚ M) : NumberField M where
  to_finiteDimensional := h

theorem isOfFinOrder_fbar {g : ℕ} [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

section Iota

theorem mem_of_monoidHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (t : Formalism.CyclotomicNorms.Fbar g →* Ω) (x : Formalism.CyclotomicNorms.Fbar g) : t x ∈ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
    rcases eq_or_ne (t 0) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
  · exact mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])

def redHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω) :
    Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l where
  toFun x := redThrough B κ (t x)
  map_one' := by rw [map_one]; exact redThrough_one B κ
  map_mul' x y := by
    rw [map_mul]; exact redThrough_mul B κ (mem_of_monoidHom B t x) (mem_of_monoidHom B t y)

end Iota

theorem redHom_inj {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [hl : Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (x y : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) (hy : y ≠ 0)
    (cx : (orderOf x).Coprime l) (cy : (orderOf y).Coprime l) (h : redHom B κ t x = redHom B κ t y) : x = y := by
  let ρ : B →+* Formalism.CyclotomicNorms.Fbar l := κ.toRingHom.comp (IsLocalRing.residue B)
  have hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩ := fun z hz => by
    unfold redThrough; rw [dite_eq_left hz]; rfl
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hmem := mem_of_monoidHom B t (x * y⁻¹)
  have hprim : IsPrimitiveRoot (t (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact hm
  have hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim
  have hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1 := by
    have hxy : x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hy0 : redHom B κ t y ≠ 0 := by
      intro h0
      have hyo := (isOfFinOrder_fbar hy).orderOf_pos
      have : redHom B κ t y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h0, zero_pow hyo.ne'] at this
      exact zero_ne_one this
    have h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y := by
      rw [← map_mul, ← hxy, one_mul, h]
    have h3 := mul_right_cancel₀ hy0 h2
    rw [← hρ]
    exact h3
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]
  have hn1 : n = 1 := IsPrimitiveRoot.one_left_iff.1 h3
  rw [hn, orderOf_eq_one_iff] at hn1
  calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    _ = y := by rw [hn1, one_mul]

end GlobalTheory.ParRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem ss_exists : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := _root_.GlobalTheory.SemisimplificationExists.exists_semisimplification

theorem indep : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := _root_.GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place

theorem ssRep_spec {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep (ssRep ρ) ∧ ρ.ker ≤ (ssRep ρ).ker ∧
    ∀ g, (ssRep ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  Classical.epsilon_spec (ss_exists ρ)

theorem castMt_eq {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j))
    (M' : Submodule ℂ (D.what₂.Mt μ' j')) (h : HEq M M') : castMt h1 h2 M = M' := by
  subst h1; subst h2; exact eq_of_heq h

theorem isOpen_ker_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {O : Type} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (I : Ideal O) (hI : IsOpen (I : Set O)) {k : Type} [CommRing k] (φ : O →+* k)
    (hφ : I ≤ RingHom.ker φ) {a : ℕ} (ρ : Γ →* GL (Fin a) O)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin a) (Fin a) O)) :
    IsOpen ((mapRep φ ρ).ker : Set Γ) := by
  let U : Set Γ := ⋂ i : Fin a, ⋂ j : Fin a, (fun g => (ρ g : Matrix (Fin a) (Fin a) O) i j - (1 : Matrix (Fin a) (Fin a) O) i j) ⁻¹' (I : Set O)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hI.preimage ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hρ)).sub continuous_const
  have h1 : (1 : Γ) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, map_one, Units.val_one, sub_self]
    intro i j; exact I.zero_mem
  have hsub : U ⊆ ((mapRep φ ρ).ker : Set Γ) := by
    intro g hg
    simp only [U, Set.mem_iInter, Set.mem_preimage] at hg
    show mapRep φ ρ g = 1
    apply Units.ext
    ext i j
    have := hφ (hg i j)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    simp only [mapRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one]
    change φ ((ρ g : Matrix (Fin a) (Fin a) O) i j) = (1 : Matrix (Fin a) (Fin a) k) i j
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1) hsub)

theorem isSSRep_one {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} : IsSSRep (1 : Γ →* GL (Fin a) k) := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  exact ⟨W', fun g v hv => by simpa using hv, hW'⟩

theorem fbCast_trans {p q r : ℕ} (h1 : p = q) (h2 : q = r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (x : Fb p hp) :
    fbCast h2 hq hr (fbCast h1 hp hq x) = fbCast (h1.trans h2) hp hr x := by
  subst h1; subst h2; rfl

theorem plκ_cast (D : D7) (Pl : PlSide D) {lam lam' : D.what₂.places.Pl} (h : lam = lam') {p : ℕ} (hp : p.Prime)
    (h1 : D.what₂.places.resChar lam = p) (h1' : D.what₂.places.resChar lam' = p) (z z' : ℂ) (hz : z ∈ Pl.plB lam)
    (hz' : z' ∈ Pl.plB lam') (hd : z - z' ∈ (Pl.plB lam).nonunits) :
    fbCast h1 (D.what₂.places.resChar_prime lam) hp (Pl.plκ lam (IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩)) =
      fbCast h1' (D.what₂.places.resChar_prime lam') hp (Pl.plκ lam' (IsLocalRing.residue (Pl.plB lam') ⟨z', hz'⟩)) := by
  subst h
  have : IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩ = IsLocalRing.residue (Pl.plB lam) ⟨z', hz'⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hd
    simpa using hd
  rw [this]

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B).charpoly = (ρ g : Matrix (Fin a) (Fin a) A).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  rfl

theorem isSSRep_rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    IsSSRep (rbarOf Y σ lam) := by
  unfold rbarOf
  split_ifs with h
  · exact (ssRep_spec _).1
  · exact isSSRep_one

set_option maxHeartbeats 1000000 in
theorem rbar_tie_at (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X)
    (hCheb : GlobalTheory.RowTie.ChebSplit D.nd) (hloc : ∀ i σ w, Y.locW i σ w = Rw.locR σ w)
    (hplB : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y))
    (i : X.nd.Loc) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (hP : HasParamW X.nd Y.naut i σ Sig)
    (hR : IsRepOfSig X.nd Y.naut i Sig ρ) (g : G D.host.E X.nd.Om) :
    ((rbarOf Y σ (X.nd.w i) g : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
        (fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out).toRingHom =
      (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.map ((Y.naut.kFbar i).comp (IsLocalRing.residue (X.nd.O i))) := by
  have hex : RbarData Y σ (X.nd.w i) := ⟨i, rfl, Sig, ρ, hP, hR⟩
  unfold rbarOf
  rw [dite_eq_left hex, (ssRep_spec _).2.2 g, charpoly_mapRep, Polynomial.map_map]
  have hw0 := hex.choose_spec.1
  have hs := hex.choose_spec.2.choose_spec.choose_spec
  generalize hex.choose_spec.2.choose_spec.choose = ρ0 at hs ⊢
  generalize hex.choose_spec.2.choose = Sig0 at hs ρ0 ⊢
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  obtain ⟨hz0, e0⟩ := hplB hex.choose ((ρ0 g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O hex.choose)).charpoly.coeff n)
  obtain ⟨hz, e⟩ := hplB i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n)
  rw [← e0, ← e, fbCast_trans, fbCast_trans]
  exact plκ_cast D Pl hw0 _ _ _ _ _ hz0 hz
    (indep D Rw Pl X Y hCheb hloc hplB σ _ i hw0 Sig0 Sig ρ0 ρ hs.1 hs.2 hP hR g n)


set_option maxHeartbeats 1000000 in
theorem locTy_exists : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), BlocksUnique D → GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (Pl.ι (X.nd.w i))) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → (∀ i k v, X.nd.gam0 i (D.naut.plGw k v) = D.ntypes.tg k v) → (∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))) → (∀ (i i' : X.nd.Loc) (σ' : (lay0 D).ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P)) → ∃ Z : LocTy Y, BcTie X.nd Y.naut Z.ntypes ∧ RbarTie X.nd Y.naut Z.ntypes ∧ MtParTie X.nd Y.naut Z.ntypes ∧ ∀ σ lam, IsSSRep (Z.rbar σ lam) := by
  intro D Rw Pl X Y hBU hCheb hloc hiota hplB hgam hchi hMt
  refine ⟨{ bc := bcOf D Rw, bc_pos := ?_, bc_sum := ?_, rbar := rbarOf Y, rbar_open := ?_, heckeLoc_gamma_places := hgam, chiT_tg := ?_, MtPar := mtParOf Y }, ?_, ?_, ?_, ?_⟩
  · intro σ p hp
    unfold bcOf at hp
    split_ifs at hp with h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
      obtain ⟨h1, h2, -⟩ := h.choose_spec.1 q hq
      exact ⟨h1, h2⟩
    · rw [Multiset.mem_singleton] at hp; subst hp
      refine ⟨?_, Nat.one_pos⟩
      have := D.R.m_add_three_le_k; have := D.R.two_le_m
      simp only [Ranks.r]; omega
  · intro σ
    unfold bcOf
    split_ifs with h
    · have := h.choose_spec.2.1
      simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      simpa [rankIso, Function.comp_def] using this
    · simp
  · intro σ lam
    show IsOpen (((rbarOf Y σ lam).ker : Subgroup _) : Set (G D.host.E X.nd.Om))
    unfold rbarOf
    split_ifs with h
    · apply Subgroup.isOpen_mono (ssRep_spec _).2.1
      have hc := h.choose_spec.2.choose_spec.choose_spec.2.1
      refine isOpen_ker_mapRep (IsLocalRing.maximalIdeal (X.nd.O h.choose)) ?_ _ ?_ _ hc
      · have := (isAdic_iff.1 (X.nd.O_adic h.choose)).1 1
        simpa using this
      · intro y hy
        rw [RingHom.mem_ker]
        simp [(IsLocalRing.residue_eq_zero_iff y).2 hy]
    · simp [MonoidHom.ker_one]
  · intro i k v hk
    obtain ⟨u, hu, he⟩ := hchi i k v hk
    rcases hu with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · intro i σ Sig hP hcsd hinf
    have hg : BcGood D Rw σ Sig := ⟨fun p hp => ⟨(hP.1 p hp).1, (hP.1 p hp).2, hcsd p hp, hinf p hp⟩, hP.2.1,
      fun w hw => (hP.2.2 w hw).trans (hloc i σ w)⟩
    have hex : ∃ Sig, BcGood D Rw σ Sig := ⟨Sig, hg⟩
    show bcOf D Rw σ = _
    unfold bcOf
    rw [dite_eq_left hex]
    have h0 := hex.choose_spec
    refine hBU _ _ (fun p hp => ?_) h0.2.1 hg.2.1 (fun w hw => (h0.2.2 w hw).trans (hg.2.2 w hw).symm)
    rcases List.mem_append.1 hp with hp | hp
    · exact h0.1 p hp
    · exact hg.1 p hp
  · intro i σ Sig ρ hP hR
    refine ⟨?_, rbar_tie_at D Rw Pl X Y hCheb hloc hplB i σ Sig ρ hP hR⟩
    exact isSSRep_rbarOf Y σ (X.nd.w i)
  · intro i σ'
    show mtParOf Y (X.nd.mu i) (X.nd.j i) σ' = mtSup Y i σ'
    have hex : ∃ i', X.nd.mu i' = X.nd.mu i ∧ X.nd.j i' = X.nd.j i := ⟨i, rfl, rfl⟩
    unfold mtParOf
    rw [dite_eq_left hex]
    exact castMt_eq _ _ _ _ (hMt _ _ σ' hex.choose_spec.1 hex.choose_spec.2)
  · exact fun σ lam => isSSRep_rbarOf Y σ lam

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem pr_lvC_eq_lv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  intro B X I hI hP l Z H F hS hC u i h1 h2 v c
  have hi := le_of_succ_m h2
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hL⟩ := hsp i hi
  have hlat := (hL u I.mu0).1 c
  obtain ⟨hF, hFC⟩ := hS u
  have hcl : clsCrd (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hlat
  have hres := hF.res
  have hsep := sepElt_of_ok l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hLd : Ld (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.Lsh := by
    show dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (clsCrd (I.rec7 l Z) u i hi c) = _
    rw [hg, hcl]
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ _
  have hPv : (F u).atT.Pv v = (show (B.primes X).vT u from v).1.asIdeal := by
    ext x
    show (F u).atT.res v x = 0 ↔ _
    rw [hres]
    exact Ideal.Quotient.eq_zero_iff_mem (I := (show HeightOneSpectrum (𝓞 B.fields.E) from v.1).asIdeal)
  have hLk : Formalism.L2.Forms.Lk (F u).atT i hi v c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.LshKer v := by
    rw [lv_LshKer_eq _ hsep v]
    show clsCrd (I.rec7 l Z) u i hi c ⊔ (F u).atT.Pv v • Ld (I.rec7 l Z) u i hi c = _
    rw [hLd, hcl, hPv]
    rfl
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 (I.rec7 l Z).host.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hu : (F u).atT.res v s ≠ 0 := by
    rw [hres, hs]
    exact fun h => hsep.off v (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hd : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Ld (I.rec7 l Z) u i hi c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.N := fun x hx => by
    rw [hs]
    exact (((I.stp u I.mu0 i).rep c).1.1.deco).2.smul_Lsh_mem_N hsep.conj (hLd ▸ hx)
  have hk : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v := fun x hx => by
    rw [hs]
    exact (le_sup_left : _ ≤ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v) (lv_smul_LshKer_mem _ hsep v (hLk ▸ hx))
  refine ⟨fun z z' e => ?_, fun z z' e => ?_⟩
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.pr i hi v c (s • ⟨x', hx⟩) (hd x' hx)
    have e2 := (hFC.1 i h1 h2).1 v c (s • ⟨x', hx'⟩) (hd x' hx)
    rw [((F u).lv i hi).pr_smul] at e1
    rw [((F u).lvC i h1 h2).pr_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.prk i hi v c (s • ⟨x', hx⟩) (hk x' hx)
    have e2 := (hFC.1 i h1 h2).2 v c (s • ⟨x', hx'⟩) (hk x' hx)
    rw [((F u).lv i hi).prk_smul] at e1
    rw [((F u).lvC i h1 h2).prk_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)

end GlobalTheory.Mem.Col2.HAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DnFv

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj
open Formalism.HermitianLatticesTheory (localization₂ dual)

theorem dual_map_smul {F V : Type} {iF : CommSemiring F} {iV : AddCommMonoid V} {iM : Module F V} (φ : Module.Dual F V) (a : F) (y : V) :
    φ (a • y) = a * φ y := by
  rw [map_smul, smul_eq_mul]

section TD

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem dn_extF_ok (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    ((A.deco c.1 (S.rep c)).dn P (TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g)).Ok := by
  have hN := ht.dnN_eq c.1 (S.rep c) P
  refine (ht.ok c.1 (S.rep c)).dn P hM ?_ ?_ ?_ ?_
  · intro x hx y hy
    rw [← hN] at hx hy
    rw [extF_of_mem g hx, extF_of_mem g hy, extF_of_mem g ((localization₂ _ _).add_mem hx hy), redL_add hx hy, map_add (f := _)]
  · intro r x hx
    rw [← hN] at hx
    rw [extF_of_mem g hx, extF_of_mem g ((localization₂ _ _).smul_mem r hx), redL_osmul r hx, map_smul]
    rfl
  · intro x hx
    rw [← hN] at hx
    exact extF_of_notMem g hx
  · obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
      by_contra H
      push Not at H
      exact hg (LinearMap.ext H)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x.1, hN ▸ x.2, ?_⟩
    rw [extF_of_mem g (le_locP _ _ x.2), redL_coe]
    exact hz

theorem N_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.N c.1 (A.dnPt P c g) = A.dnN c.1 (S.rep c) P := by
  have h := congrArg Deco.N (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  exact h.trans (ht.dnN_eq c.1 (S.rep c) P).symm

theorem f_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.f c.1 (A.dnPt P c g) P = TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g := by
  classical
  have h := congrArg (fun d => Deco.f d P) (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  refine h.trans ?_
  simp [Deco.dn]

theorem fv_dn (ho : A.Ok T) (ht : A.Tied T) (hl : A.Laws T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) {x : Fin n → E} {s : 𝓞 E} {G : Matrix (Fin n) (Fin n) E}
    (hG : G = (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E))
    (hsx : s • x ∈ A.N (S.cl c.1 (A.dnPt P c g)).1 (S.rep (S.cl c.1 (A.dnPt P c g)))) :
    ∃ h : s • (G *ᵥ x) ∈ A.dnN c.1 (S.rep c) P,
      A.fv P (S.cl c.1 (A.dnPt P c g)) (Submodule.Quotient.mk ⟨_, hsx⟩) = g (Submodule.Quotient.mk ⟨_, h⟩) := by
  subst hG
  have hms : S.mv c.1 (A.dnPt P c g) • S.rep (S.cl c.1 (A.dnPt P c g)) = A.dnPt P c g := S.mv_smul c.1 _
  have e : (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ (s • x) =
      s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
    rw [← algebraMap_smul E s, ← algebraMap_smul E s, Matrix.mulVec_smul]
  have h1 := (ho.N_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) (s • x)).2 hsx
  rw [hms, N_dnPt ht P hM c hg, e] at h1
  refine ⟨h1, ?_⟩
  have h3 := ho.f_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) P (s • x)
  have h4 : redL (A.dnN c.1 (S.rep c) P) P.1 (s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x)) =
      Submodule.Quotient.mk ⟨_, h1⟩ := redL_coe ⟨_, h1⟩
  rw [hms, f_dnPt ht P hM c hg, e, extF_of_mem g (le_locP _ _ h1), h4] at h3
  exact (fv_mk hl P _ ⟨_, hsx⟩).trans h3.symm


omit [NumberField K] [StarRing K] in
theorem exists_smul_mem_N {SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)
    {y : Fin n → E} (hy : y ∈ d.Lsh) : ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.N := by
  have h := le_locP P.1 _ hy
  rw [localization_Lsh_eq_localization_N hd ha P rfl] at h
  exact (mem_locP _ _ _).1 h

end TD

end GlobalTheory.DnFv

end


open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj in
open Formalism.HermitianLatticesTheory (localization₂ dual) in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.dn_level_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ x hx
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, hc⟩ := hc i hi
  have hLc := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hmv := moveHyp_of_ok l.pr u v
  have hM : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hmv.ne, hmv.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hd : ∀ c', (((I.stp u a i).rep c').1.1.deco.1).Ok := fun c' => ((I.stp u a i).rep c').1.1.deco.2
  have hD : ∀ c', LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c')) = (((I.stp u a i).rep c').1.1.deco.1).Lsh := fun c' =>
    (@dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (fun _ => rfl) _ hgr _).trans (congrArg _ (hLc c'))
  have hx2 : (x.1 : Fin (B.R.N i) → B.fields.E) ∈ (((I.stp u a i).rep ((I.fm l u a).dn i v c.1 g)).1.1.deco.1).Lsh :=
    (SetLike.ext_iff.1 (hD _) _).1 x.2
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.DnFv.exists_smul_mem_N (hd _) ha v hx2
  have hγ' : (γ.1.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) = _ := congrArg Units.val hγ
  obtain ⟨h1, h2⟩ := GlobalTheory.DnFv.fv_dn ((l.lev u a).lev i) ((l.lev u a).tied i) ((l.fmL u a).lev i) v hM c.1 hg hγ' hsx
  let s' : 𝓞 (I.rec7 l Z).host.E := s
  have hs' : (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) ≠ 0 := mk_ne_zero hs
  have f1 : ((I.fm l u a).fv i v _ (L.pr v _ (s' • x)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * (I.fm l u a).fv i v _ (L.pr v _ x) :=
    (congrArg ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) (L.pr_smul v _ s' x)).trans
      (GlobalTheory.DnFv.dual_map_smul ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) _ _)
  let z : ↥(LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) := ⟨_, hx⟩
  have f2 : (g (L.prk v c.1 (s' • z)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * g (L.prk v c.1 z) :=
    (congrArg g (L.prk_smul v c.1 s' z)).trans (GlobalTheory.DnFv.dual_map_smul g _ _)
  refine mul_left_cancel₀ hs' (f1.symm.trans (Eq.trans ?_ f2))
  have e1 := hL.1 v _ (s' • x) hsx
  have e2 := hL.2 v c.1 (s' • z) h1
  exact (congrArg _ e1).trans (h2.trans (congrArg g e2.symm))
end

