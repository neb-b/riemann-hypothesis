module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.ConjPlaceRed

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_conj_zero (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (hs : resS F w s = 0) : resS F w' t = 0 := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hs ⊢
  exact h3 hs

theorem resS_conj_ite (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (b : Prop) [Decidable b] (hs : resS F w s = if b then 1 else 0) : resS F w' t = if b then 1 else 0 := by
  let c : Formalism.L2.Herm.intAf F E := if b then 1 else 0
  have hc1 : resS F w c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hc2 : resS F w' c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [c]; split_ifs <;> simp
  have h0 := resS_conj_zero τ w w' hc (s - c) (t - c) (by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by
    rw [map_sub, hs, hc1, sub_self])
  rw [map_sub, sub_eq_zero, hc2] at h0
  exact h0

end General

variable {D : D7}

theorem crdLat_eq_latFrame (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = GlobalTheory.PlaceModel.latFrame V := by
  ext y
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v := V.frame.sum_equivFun v
    show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0
    rw [e]; exact hv
  · intro hy
    refine ⟨_, hy, ?_⟩
    show V.frame.equivFun (∑ i, y i • V.frame i) = y
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjPlaceRed

namespace GlobalTheory.ConjPlaceRed

theorem Lv_eq_latFrame (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := by
  ext y
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv]
  exact (GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm

theorem mem_Lf (D : D7) (v : Fin (Yc D 0).rank → EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) ↔
      v ∈ lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) := by
  rw [Lv_eq_latFrame]
  exact (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm

theorem mem_St_of_Kset (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (hβ : IsFrame β (GlobalTheory.PlaceModel.latFrame (Yc D 0))) (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) :
    x.1 ∈ St β := by
  have hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := hx
  have hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈
        (Formalism.L2.SG.InstExistsPf.instOf D).Lf :=
    (Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx
  refine (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)),
    fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩


set_option maxHeartbeats 1000000 in
theorem redFn_conj_eq_one : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (PP PP' : Formalism.L2.DIV.Pl D.host.E),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset →
    IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' x.1 = 1 → Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  intro D β x PP PP' hβ hx hc h1
  rw [crdLat_eq_latFrame] at hβ
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := mem_St_of_Kset D β x hβ hx
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Yc D 0).gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1 := hh
    rw [e]
    exact x.2
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i =
          resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAll
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r)

theorem map_mem_intLoc_fld {v : HeightOneSpectrum (𝓞 F)} {c : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v) :
    Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) (IsScalarTower.toAlgHom F E (Fld P)) c ∈
      intLoc F (Fld P) v := by
  refine intLoc_induction (p := fun c => Algebra.TensorProduct.map (AlgHom.id F (Fv F v))
      (IsScalarTower.toAlgHom F E (Fld P)) c ∈ intLoc F (Fld P) v) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hc
  rw [Algebra.TensorProduct.map_tmul]
  exact tmul_mem_intLoc ha ⟨algebraMap E (Fld P) x, x.2.algebraMap⟩

theorem eventually_mem_intLoc_iff_coordEquiv_mem :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P,
      y ∈ intLoc F (Fld P) v ↔ coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  let b := RingOfIntegers.basis (Fld P)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_one_tmul_mem_intLoc (F := F) ((powB P).repr (b j : Fld P) i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (E := Fld P) (powB P i)] with v h1 h2 y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy i
    rw [coordEquiv_apply]
    refine intLoc_induction (p := fun y => coordF P (Fv F v) i y ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
    rw [coordF_tmul]
    have e : (powB P).repr (x : Fld P) i = ∑ j, b.repr x j • (powB P).repr (b j : Fld P) i := by
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [← zsmul_eq_mul, map_zsmul]
    rw [e, TensorProduct.tmul_sum]
    refine sum_mem fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    refine zsmul_mem ?_ _
    have e2 : a ⊗ₜ[F] ((powB P).repr (b j : Fld P) i) =
        (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] (powB P).repr (b j : Fld P) i) := by simp
    rw [e2]
    exact mul_mem (tmul_mem_intLoc ha 1) (h1 i j)
  · intro h
    rw [← coordInv_coordF P (Fv F v) y]
    refine sum_mem fun i _ => ?_
    rw [smul_eq_map_mul]
    exact mul_mem (map_mem_intLoc_fld P (h i)) (h2 i)

end GlobalTheory.TrUnitLat

theorem GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v :=
  fun F E _ _ _ _ _ σ r P => GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem P
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjReord

open Matrix Formalism.L2.Herm

section Perm

variable {n : ℕ}

theorem sum_perm_one (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∑ k, if f k = j then (if i = f k then (1 : R) else 0) else 0) = if i = j then 1 else 0 := by
  rw [Equiv.sum_comp f (fun m => if m = j then (if i = m then (1 : R) else 0) else 0)]
  simp

def pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : GL (Fin n) R where
  val := (1 : Matrix (Fin n) (Fin n) R).submatrix id f
  inv := (1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm
  val_inv := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f i j
  inv_val := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f.symm i j

theorem pmat_inv (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : (pmat R f)⁻¹ = pmat R f.symm := by
  ext i j
  rfl

theorem conj_pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pmat R f)⁻¹ * g * pmat R f : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b = (g : Matrix (Fin n) (Fin n) R) (f a) (f b) := by
  rw [pmat_inv, Units.val_mul, Units.val_mul]
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm * (g : Matrix (Fin n) (Fin n) R) *
    (1 : Matrix (Fin n) (Fin n) R).submatrix id f) a b = _
  simp [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply]

theorem bc_pmat {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : Equiv.Perm (Fin n)) :
    Formalism.UG.bc φ (pmat R f) = pmat S f := by
  apply Units.ext
  ext i j
  simp only [Formalism.UG.bc, pmat] at *
  by_cases h : i = f j <;> simp [Matrix.one_apply, h]

theorem pmat_mulVec (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (v : Fin n → R) :
    ((pmat R f.symm : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v = fun i => v (f i) := by
  funext i
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm *ᵥ v) i = v (f i)
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Equiv.eq_symm_apply]

end Perm

section Frame

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ y : GL (Fin n) (intAf F E)) :
    frGL (β * intGL F E n σ) y = frGL β (σ * y * σ⁻¹) := by
  show β * intGL F E n σ * intGL F E n y * (β * intGL F E n σ)⁻¹ = β * intGL F E n (σ * y * σ⁻¹) * β⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem St_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) :
    St (β * intGL F E n σ) = St β := by
  ext x
  simp only [St, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨σ * y * σ⁻¹, (frGL_mul_int β σ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨σ⁻¹ * y * σ, ?_⟩
    rw [frGL_mul_int]
    congr 1
    group

theorem redFn_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) (PP : Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n σ) PP x = (Formalism.UG.bc (resS F PP) σ)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) σ := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have hy : frGL β y = frGL (β * intGL F E n σ) (σ⁻¹ * y * σ) := by
      rw [frGL_mul_int]
      congr 1
      group
    rw [redFn_frGL β PP y, hy, redFn_frGL]
    simp only [map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n σ) := by rwa [St_mul_int]
    simp [redFn, ext1, hx, hx']

theorem isFrame_mul_pmat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ)
    (f : Equiv.Perm (Fin n)) : IsFrame (β * intGL F E n (pmat _ f)) Λ := by
  unfold Formalism.L2.DIV.IsFrame at h ⊢
  intro x
  have e : (((β * intGL F E n (pmat _ f))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x =
      fun i => (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) (f i) := by
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv (intGL F E n) (pmat _ f), pmat_inv]
    unfold intGL
    rw [bc_pmat, pmat_mulVec]
  rw [h x, e]
  exact ⟨fun hx i => hx (f i), fun hx i => by simpa using hx (f.symm i)⟩

end Frame

section Level

variable {D : D7}

theorem rankBlock_val_eq_submatrix_of_le_rank {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (M : GL (Fin n) κ) :
    ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) =
      (M : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  apply upper_block_val_submatrix
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blk2, hi] at hij

theorem blockTri_all {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (M : GL (Fin n) κ) :
    M ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blkOf, hi] at hij

def fperm {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) : Equiv.Perm (Fin n) :=
  ((finCongr (le_antisymm hr hn)).symm.trans π.symm).trans (finCongr (le_antisymm hr hn))

theorem fperm_castLE {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) (a : Fin r) :
    fperm hr hn π (Fin.castLE hr (π a)) = Fin.castLE hr a := by
  have h1 : (finCongr (le_antisymm hr hn)).symm (Fin.castLE hr (π a)) = π a := Fin.ext (by simp)
  simp only [fperm, Equiv.trans_apply, h1, Equiv.symm_apply_apply]
  exact Fin.ext (by simp)

theorem reord_rTup {n : ℕ} (L : LevDat D.host.E ℂ n) (hn : n ≤ L.r) (β : GL (Fin n) (EAf D))
    (π : Equiv.Perm (Fin L.r)) (x : GL (Fin n) (EAf D)) :
    reord π (rTup (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) L x) = rTup β L x := by
  funext PP
  apply Units.ext
  ext a b
  show (upperLeftBlock L.hr (redFn (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) PP.1 x)).1 (π a) (π b) =
    (upperLeftBlock L.hr (redFn β PP.1 x)).1 a b
  rw [rankBlock_val_eq_submatrix_of_le_rank L.hr hn, rankBlock_val_eq_submatrix_of_le_rank L.hr hn, redFn_mul_int, bc_pmat]
  simp only [Matrix.submatrix_apply]
  rw [conj_pmat, fperm_castLE, fperm_castLE]

theorem rank_zeroth_component_eq : (Yc D 0).rank ≤ D.R.r := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  show (D.sp.Y (min 0 D.R.m)).rank ≤ D.R.r
  rw [Nat.zero_min, h]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

end Level

section Main

variable {D : D7}

def r0 {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    G0 Lc.Pg D.R.r :=
  fun PP => upperLeftBlock (r_le_Y 0) (redFn β PP.1 x)

theorem mem_levelSubgroup_principalDatum_iff {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    κ ∈ levS (Yc D 0) β (Lc.dat0 P) ↔
      (κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β) ∧
        r0 Lc β (finE (Yc D 0) κ) ∈ P.H := by
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  have hblk : ∀ PP ∈ (Lc.dat0 P).Pg,
      redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blkOf (Lc.dat0 P).r (Lc.dat0 P).t) :=
    fun PP _ => blockTri_all _ (rank_zeroth_component_eq (D := D)) _
  have hQ : ∀ PP ∈ (Lc.dat0 P).Q, redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blk2 (Lc.dat0 P).r) := by
    intro PP h
    simp [LevCh.dat0, datY] at h
  rw [Formalism.IndefR.Links.levS, Formalism.IndefR.Lev.levG, SetLike.mem_coe, Formalism.IndefR.Lev.mem_levA, Formalism.L2.DIV.mem_lev,
    Formalism.L2.DIV.mem_parLev, hP]
  exact ⟨fun ⟨h1, ⟨h2, h3, _, _⟩, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
    fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, ⟨h2, h3, hblk, hQ⟩, h4⟩⟩

theorem principalRowLevelCharacter_trivial {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) β (Lc.dat0 P) κ = ((ext1 P.H P.chi (r0 Lc β (finE (Yc D 0) κ)) : ℂˣ) : ℂ) := by
  have hs : (Lc.dat0 P).s = 0 := rfl
  have hQ : (Lc.dat0 P).Q = ∅ := rfl
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  rw [Formalism.IndefR.Lev.levChi, levFn, hs, hQ, hP]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem level_eq_of_reord {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r))
    (hH : ∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) (hchi : ∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩)
    (β₂ β₃ : GL (Fin (Yc D 0).rank) (EAf D)) (hSt : St β₂ = St β₃)
    (hkey : ∀ x, reord π (r0 Lc β₂ x) = r0 Lc β₃ x) (κ : GA D (Yc D 0)) :
    (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧
      levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  refine ⟨?_, ?_⟩
  · rw [mem_levelSubgroup_principalDatum_iff, mem_levelSubgroup_principalDatum_iff, hSt, hH, hkey]
  · rw [principalRowLevelCharacter_trivial, principalRowLevelCharacter_trivial]
    by_cases hg : r0 Lc β₂ (finE (Yc D 0) κ) ∈ P.H
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∈ P'.H := by
        rw [← hkey]
        exact (hH _).1 hg
      have e : (⟨reord π (r0 Lc β₂ (finE (Yc D 0) κ)), (hH _).1 hg⟩ : P'.H) = ⟨r0 Lc β₃ (finE (Yc D 0) κ), hg'⟩ :=
        Subtype.ext (hkey _)
      rw [extendOne_of_mem _ hg, extendOne_of_mem _ hg', hchi _ hg ((hH _).1 hg), e]
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∉ P'.H := by
        rw [← hkey]
        exact fun h => hg ((hH _).2 h)
      unfold ext1
      rw [dite_eq_right hg, dite_eq_right hg']

end Main

theorem exists_frame_reord : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  intro D T Lc P P' π hH hchi β₃ hβ
  exact ⟨β₃ * intGL _ _ _ (pmat _ (fperm (Lc.dat0 P).hr (rank_zeroth_component_eq (D := D)) π)), isFrame_mul_pmat hβ _,
    fun κ => level_eq_of_reord Lc P P' π hH hchi _ β₃ (St_mul_int _ _)
      (fun x => reord_rTup (Lc.dat0 P) (rank_zeroth_component_eq (D := D)) β₃ π x) κ⟩

end GlobalTheory.SeeConjReord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumeratiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signCompatible_numbering_decreasing_enumeration : ∀ (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ), l₁.length = p → l₂.length = q → IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) → IsEnum (parOf br cj l₁ l₂ c) lamM ε → ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  first | exact @GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | exact GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | (intros; apply GlobalTheory.ArchRec.EnumBlocks.exists_isOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := _root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects

end GlobalTheory
end

