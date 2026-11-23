module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoords
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem ptAt_complMap (b : Fv F v) : ptAt hw h (complMap h b) = GlobalTheory.LatVac.liftV v b • (1 : AE F E) := by
  have hat : At (evFin F v) (GlobalTheory.LatVac.liftV v b • (1 : AE F E)) := by
    intro u hu
    rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v b u hu, zero_smul]
  rw [← ptAt_locW hw h hat]
  congr 1
  change complMap h b = toCompl h (compFin F E v (GlobalTheory.LatVac.liftV v b • (1 : AE F E)))
  rw [GlobalTheory.ThK.compFin_smul, map_one, GlobalTheory.LatVac.evFin_liftV, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    toCompl_tmul, smul_eq_mul, mul_one, map_one, mul_one]

theorem locW_smul_inclR (a : AF F) (e : E) :
    locW h (a • inclR (F := F) (AF F) e) = complMap h (evFin F v a) * algebraMap E _ e := by
  change toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] e))) = _
  rw [GlobalTheory.ThK.compFin_smul, GlobalTheory.AdelicU.Supp.compFin_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, toCompl_tmul]

theorem mul_vecMulVec_mul {R : Type} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin m) R) (N : Matrix (Fin k) (Fin k) R)
    (p : Fin m → R) (q : Fin k → R) : M * Matrix.vecMulVec p q * Nᵀ = Matrix.vecMulVec (M *ᵥ p) (N *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mul_transpose_mul_eq_sum {R : Type} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin k) (Fin k) R) (x : Matrix (Fin k) (Fin m) R) :
    A * xᵀ * Bᵀ = ∑ i, ∑ j, x j i • Matrix.vecMulVec (Aᵀ i) (Bᵀ j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem smul_mem_latAtV {t : w.adicCompletion E} (ht : t ∈ Formalism.UG.Ov E w) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X Y v) : ptAt hw h t • γ ∈ latAtV X Y v := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective h t
  have hy := (InertChart.mem_intLoc_iff hw h y).2 ht
  refine intLoc_induction (p := fun y => ∀ γ ∈ latAtV X Y v, ptAt hw h (toCompl h y) • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy γ hγ
  · intro a ha o γ hγ
    rw [toCompl_tmul, mul_comm, ← inclR_mul_ptAt, ptAt_complMap]
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * a', ?_, ?_, (o • x), X.L.smul_mem o hx, y, hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem ha hv
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [show algebraMap (𝓞 E) E o = (o : E) from rfl]
        ring
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro γ hγ; rw [map_zero, map_zero, zero_smul]; exact zero_mem _
  · intro y z hy hz γ hγ; rw [map_add (f := _), map_add (f := _), add_smul]; exact add_mem (hy γ hγ) (hz γ hγ)
  · intro y hy γ hγ; rw [map_neg, map_neg, neg_smul]; exact neg_mem (hy γ hγ)

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem ptAt_algebraMap (e : E) :
    ptAt hw h (algebraMap E (w.adicCompletion E) e) = GlobalTheory.LatVac.liftV v 1 • inclR (F := F) (AF F) e := by
  have := inclR_mul_ptAt hw h e 1
  rw [mul_one, ← (complMap h).map_one, ptAt_complMap, mul_smul_comm, mul_one] at this
  exact this.symm

theorem vecMulVec_mem {p : Fin n → w.adicCompletion E} (hp : p ∈ latAt w X.L) {q : Fin d → w.adicCompletion E}
    (hq : q ∈ latAt w Y.L) : (Matrix.vecMulVec p q).map (ptAt hw h) ∈ latAtV X Y v := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨x, hx, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨y, hy, rfl⟩ := hq
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1, ?_, x, hx, y, hy, ?_⟩
      · rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, ← map_mul, ptAt_algebraMap]
    | zero =>
      convert zero_mem (latAtV X Y v) using 1
      ext k l; simp [Matrix.vecMulVec_apply]
    | add q q' _ _ h1 h2 =>
      convert add_mem h1 h2 using 1
      ext k l; simp [Matrix.vecMulVec_apply, mul_add]
    | smul t q _ h1 =>
      convert smul_mem_latAtV hw h X Y t.2 h1 using 1
      ext k l
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
      congr 1
      rw [Subring.smul_def, smul_eq_mul]
      ring
  | zero =>
    convert zero_mem (latAtV X Y v) using 1
    ext k l; simp [Matrix.vecMulVec_apply]
  | add p p' _ _ h1 h2 =>
    convert add_mem h1 h2 using 1
    ext k l; simp [Matrix.vecMulVec_apply, add_mul]
  | smul t p _ h1 =>
    convert smul_mem_latAtV hw h X Y t.2 h1 using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
    congr 1
    rw [Subring.smul_def, smul_eq_mul]
    ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat


open GlobalTheory.InertCoord in
theorem kap_mem_latAtV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ v w hw h n d X Y A Bm hA hB x
  have col : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ i, (C : Matrix (Fin m) (Fin m) (w.adicCompletion E))ᵀ i ∈ latAt w L := by
    intro m L C hC i
    have := (hC (Pi.single i 1)).1 fun k => by
      by_cases e : k = i
      · subst e; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _
    rwa [Matrix.mulVec_single_one] at this
  have inv : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ z ∈ L, ∀ k, ((↑C⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ
        fun i => algebraMap E (w.adicCompletion E) (z i)) k ∈ Formalism.UG.Ov E w := by
    intro m L C hC z hz
    refine (hC _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  constructor
  · intro hx
    rw [kap_apply, mul_transpose_mul_eq_sum]
    change _ ∈ (latAtV X Y v).comap (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom)
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    change (x j i • Matrix.vecMulVec _ _).map (ptAt hw h) ∈ latAtV X Y v
    convert smul_mem_latAtV hw h X Y (hx j i) (vecMulVec_mem hw h X Y (col hA i) (col hB j)) using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  · intro hk i j
    let Ψ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (w.adicCompletion E) := fun γ =>
      (↑A⁻¹ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * AddMonoidHom.mapMatrix (locW h).toAddMonoidHom γ *
        (↑Bm⁻¹ : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ
    have hΨ : ∀ γ ∈ latAtV X Y v, ∀ k l, Ψ γ k l ∈ Formalism.UG.Ov E w := by
      intro γ hγ
      induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, ha, p, hp, q, hq, rfl⟩ := hz
        have e1 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (a • incM F (Matrix.vecMulVec p q)) =
            complMap h (evFin F v a) • Matrix.vecMulVec (fun i => algebraMap E (w.adicCompletion E) (p i))
              (fun i => algebraMap E (w.adicCompletion E) (q i)) := by
          refine Matrix.ext fun k l => ?_
          change locW h (a • inclR (F := F) (AF F) (p k * q l)) = _
          rw [locW_smul_inclR, map_mul]
          simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
        intro k l
        simp only [Ψ, e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, Matrix.smul_apply,
          Matrix.vecMulVec_apply, smul_eq_mul]
        exact mul_mem (complMap_mem h ha) (mul_mem (inv hA p hp k) (inv hB q hq l))
      | zero => intro k l; simp [Ψ]
      | add x y _ _ hx hy =>
        intro k l
        simp only [Ψ, map_add (f := _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hx k l) (hy k l)
      | neg x _ hx =>
        intro k l
        simp only [Ψ, map_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
        exact neg_mem (hx k l)
    have e : Ψ (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = xᵀ := by
      have e2 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
          (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
        refine Matrix.ext fun k l => ?_
        simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, kap_apply, RingHom.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, locW_ptAt]
      simp only [Ψ, e2]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have := hΨ _ hk j i
    rw [e] at this
    exact this

end GlobalTheory.InertLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat

section Halves

variable {D : D7}

theorem hO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) : hO S₁ S₂ z (cA D a • y) = hO S₁ S₂ (a • z) y := by
  unfold hO
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  ring

theorem symplO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) :
    symplO S₁ S₂ z (cA D a • y) = symplO S₁ S₂ (a • z) y := by
  unfold symplO
  rw [hO_cA_smul]

theorem symplO_zero_right' (S₁ S₂ : HSp D) (z : WO S₁ S₂) : symplO S₁ S₂ z 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_smul_self {m n : ℕ} {b : AE D} (hb : b * b = b) (x : Matrix (Fin m) (Fin n) (AE D)) : IsHalf b (b • x) :=
  fun p q => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hb]

theorem smul_of_isHalf {m n : ℕ} {b : AE D} {x : Matrix (Fin m) (Fin n) (AE D)} (hx : IsHalf b x) : b • x = x :=
  Matrix.ext fun p q => hx p q

theorem smul_eq_zero_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) (c : AF D.host.F) (hc : evFin D.host.F v c = 0) : c • x = 0 := by
  have h0 : c * GlobalTheory.LatVac.liftV v 1 = 0 := GlobalTheory.LatVac.at_liftV v 1 c hc
  ext p q
  rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def]
  have e : algebraMap (AF D.host.F) (AE D) c * x p q =
      b * algebraMap (AF D.host.F) (AE D) (c * GlobalTheory.LatVac.liftV v 1) * x p q := by
    conv_lhs => rw [← hx p q, ← hb]
    rw [map_mul]
    ring
  rw [e, h0, map_zero, mul_zero, zero_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem at_of_mixHalf (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : Pt G i j} (hu : u ∈ mixHalf e b) :
    At (evFin D.host.F v) u := by
  intro c hc
  apply (maps e).injective
  rw [map_smul, map_zero, maps_apply, Prod.smul_mk, smul_eq_zero_of_isHalf v hb hu.1 c hc,
    smul_eq_zero_of_isHalf v hb hu.2 c hc, Prod.mk_zero_zero]

theorem ofMaps_smul_mem (e : Num G i j) {b : AE D} (hb : b * b = b) (x₁ : HomV G i j) (x₂ : HomW G i j) :
    ofMaps e (b • x₁, b • x₂) ∈ mixHalf e b := by
  refine ⟨?_, ?_⟩
  · show IsHalf b (mapV e (ofMaps e _))
    rw [mapV_ofMaps]
    exact isHalf_smul_self hb _
  · show IsHalf b (mapW e (ofMaps e _))
    rw [mapW_ofMaps]
    exact isHalf_smul_self hb _

theorem ofMaps_add_ofMaps (e : Num G i j) (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : Pt G i j}
    (hu : At (evFin D.host.F v) u) :
    ofMaps e (a • mapV e u, a • mapW e u) + ofMaps e (cA D a • mapV e u, cA D a • mapW e u) = u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  have hℓu : GlobalTheory.LatVac.liftV v 1 • u = u := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  apply (maps e).injective
  refine Prod.ext ?_ ?_
  · show mapV e (_ + _) = mapV e u
    rw [mapV_add, mapV_ofMaps, mapV_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapV_smul, hℓu]
  · show mapW e (_ + _) = mapW e u
    rw [mapW_add, mapW_ofMaps, mapW_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapW_smul, hℓu]

theorem infPart_algebraMap_liftV (v : Pl D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) = 0 :=
  GlobalTheory.LatVac.infPart_pair (GlobalTheory.AdelicU.singleFin v 1) 1

theorem map_infPart_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) : x.map (infPart D) = 0 := by
  ext p q
  rw [Matrix.map_apply, Matrix.zero_apply, ← hx p q, ← hb, map_mul, map_mul, infPart_algebraMap_liftV, mul_zero, zero_mul]

theorem mapV_mem_latV_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid (i + 1) (j + 1))))
    (hT : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapV e x ∈ latV G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.1) fun l hl => ?_
  have hy : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact isHalf_smul_self hcc _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact fun p q => mul_zero _
  have hyl : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact zero_mem _
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.1, symplO_zero_right',
    add_zero] at h
  exact h

theorem mapW_mem_latW_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spV₁ G i j) (G.Λ (.grid (i + 1) j)))
    (hT : IsSelfDualC (spW G i j) (G.Λ (.grid (i + 1) (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapW e x ∈ latW G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.2) fun l hl => ?_
  have hy : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact fun p q => mul_zero _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact isHalf_smul_self hcc _
  have hyl : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact zero_mem _
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.2, symplO_zero_right',
    zero_add] at h
  exact h

theorem halves_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (v : Pl D.host.F) (a : AE D), IsSplitIdem D a →
    a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) →
    (∀ u ∈ mixHalf e a, At (evFin D.host.F v) u) ∧ (∀ u ∈ mixHalf e (cA D a), At (evFin D.host.F v) u) ∧
    (∀ u : Pt G i j, At (evFin D.host.F v) u → ∃ x ∈ mixHalf e a, ∃ y ∈ mixHalf e (cA D a), u = x + y) ∧
    (∀ x ∈ mixHalf e a, (∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → W.ψ (sympPt Γ x y) = 1) → x ∈ latPt e v) ∧
    ∀ u : Pt G i j, ofMaps e (a • mapV e u, a • mapW e u) ∈ mixHalf e a ∧
      (∀ y ∈ mixHalf e (cA D a), sympPt Γ u y = sympPt Γ (ofMaps e (a • mapV e u, a • mapW e u)) y) ∧
      (mapV e u ∈ latV G i j → mapW e u ∈ latW G i j → ofMaps e (a • mapV e u, a • mapW e u) ∈ latPt e v) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v a ha hsum
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D a) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨fun u hu => at_of_mixHalf e v ha1 hu, fun u hu => at_of_mixHalf e v hc1 hu, fun u hu =>
    ⟨_, ofMaps_smul_mem e haa _ _, _, ofMaps_smul_mem e hcc _ _, (ofMaps_add_ofMaps e v hsum hu).symm⟩,
    fun x hx hψ => ⟨at_of_mixHalf e v ha1 hx,
      mapV_mem_latV_of_char e Γ hW hWW W.ψ_std hS hT v ha1 hcc hc1 hfc hx hψ,
      mapW_mem_latW_of_char e Γ hW hWW W.ψ_std hS₁ hT₁ v ha1 hcc hc1 hfc hx hψ⟩, fun u => ?_⟩
  refine ⟨ofMaps_smul_mem e haa _ _, fun y hy => ?_, fun hV hW' => ?_⟩
  · rw [symp_eq e Γ hW hWW, symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, ← symplO_cA_smul, ← symplO_cA_smul,
      smul_of_isHalf hy.1, smul_of_isHalf hy.2]
  · refine ⟨at_of_mixHalf e v ha1 (ofMaps_smul_mem e haa _ _), ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hV
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hW'

end Halves

end GlobalTheory.BigDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatCorrSmul
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_smul {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type}
    (_hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (hΛ : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := by

  have key : ∀ a : k', valuation k' a ≤ 1 → ∀ y ∈ Λ₂, a • y ∈ Λ₂ := fun a ha y hy =>
    Λ₂.smul_mem (⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩ : 𝒪[k']) hy
  have hc₂ : valuation k' (c₂ : k') ≠ 0 := by simp
  set u : k' := (c₂⁻¹ : k'ˣ) * j c with hu
  have hu1 : valuation k' u = 1 := by
    rw [hu, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_mul_cancel₀ hc₂]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hu1' : valuation k' u⁻¹ = 1 := by rw [map_inv₀, hu1, inv_one]
  intro x
  rw [mem_smul_lat, mem_smul_lat, ← hΛ]
  have heq : (c₂⁻¹ : k'ˣ) • (fun d => j (x (cD d))) = u • (fun d => j (((c⁻¹ : kˣ) • x) (cD d))) := by
    funext d
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, hu, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  rw [heq]
  constructor
  · intro h
    have := key u⁻¹ hu1'.le _ h
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this
  · exact key u hu1.le _

end GlobalTheory.PureMatch.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MLat3OfTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodLat.Obj3

theorem mLat3_of_tie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀) : (R.toCx3 F).MLat false :=
  fun j => GlobalTheory.GoodLat.Obj.mLat_of_tie fw F.lv2 false j

end GlobalTheory.GoodLat.Obj3
end

